//! AST-level class-structure queries: parent class, members (methods,
//! properties, constants, mixins), enclosing class at a cursor position, enum
//! backing type, and function/method parameter lists. These answer
//! structural facts directly from the parsed source and don't depend on mir.

// Reached only through the server, which is not built for wasm.
#![cfg_attr(target_family = "wasm", allow(dead_code))]
use std::collections::HashSet;
use std::sync::Arc;

use php_ast::{ClassMemberKind, EnumMemberKind, NamespaceBody, Stmt, StmtKind, Visibility};
use tower_lsp_server::ls_types::{Location, Position, Range};

use crate::document::ast::{ParsedDoc, SourceView};
use crate::lang::docblock::{docblock_before, parse_docblock};

pub fn parent_class_name(doc: &ParsedDoc, class_name: &str) -> Option<String> {
    parent_in_stmts(&doc.program().stmts, class_name)
}

fn parent_in_stmts(stmts: &[Stmt<'_, '_>], class_name: &str) -> Option<String> {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(c)
                if c.name.as_ref().map(|n| n.to_string()) == Some(class_name.to_string()) =>
            {
                return c.extends.as_ref().map(|n| n.to_string_repr().to_string());
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body
                    && let found @ Some(_) = parent_in_stmts(&inner.stmts, class_name)
                {
                    return found;
                }
            }
            _ => {}
        }
    }
    None
}

/// All members of a named class split by kind and static-ness.
#[derive(Debug, Default)]
pub struct ClassMembers {
    /// (name, is_static, has_params)
    pub methods: Vec<(String, bool, bool)>,
    /// (name, is_static)
    pub properties: Vec<(String, bool)>,
    /// Names of readonly properties (PHP 8.1+).
    pub readonly_properties: Vec<String>,
    pub constants: Vec<String>,
    /// Non-public members as `(name, is_private)`; `false` means protected.
    pub restricted_methods: Vec<(String, bool)>,
    pub restricted_properties: Vec<(String, bool)>,
    pub restricted_constants: Vec<(String, bool)>,
    /// Direct parent class name, if any.
    pub parent: Option<String>,
    /// Trait names used by this class (`use Foo, Bar;`), or the parent
    /// interfaces of an interface.
    pub trait_uses: Vec<String>,
    /// Virtual methods declared via `@method` docblock tags.
    pub doc_methods: Vec<crate::lang::docblock::DocMethod>,
    /// Classes/traits pulled in via `@mixin` docblock tags.
    pub mixins: Vec<String>,
    /// Return types of concrete methods.
    pub method_return_types: Vec<(String, String)>,
    /// True when a class/enum/trait with this name was found in the doc.
    /// Lets workspace-wide loops short-circuit once the defining doc is hit
    /// instead of continuing to scan every file.
    pub found: bool,
}

/// Return all members (methods, properties, constants) of `class_name`.
/// Also returns the direct parent class name via `ClassMembers::parent`.
pub fn members_of_class(doc: &ParsedDoc, class_name: &str) -> ClassMembers {
    let short = crate::text::fqn_short_name(class_name);
    let mut out = ClassMembers::default();
    if !declared_in_namespace_of(doc, class_name) {
        return out;
    }
    out.parent = collect_members_stmts(doc.source(), &doc.program().stmts, short, &mut out);
    out
}

/// Fully-qualified name for `name` as written inside the declaration of
/// `declaring_class` in `doc`: resolved through that file's `use` imports and
/// namespace, not the viewer's.
pub fn resolve_class_ref(doc: &ParsedDoc, declaring_class: &str, name: &str) -> String {
    if let Some(rest) = name.strip_prefix('\\') {
        return rest.to_owned();
    }
    let (first, rest) = match name.split_once('\\') {
        Some((first, rest)) => (first, Some(rest)),
        None => (name, None),
    };
    let join = |base: &str| match rest {
        Some(rest) => format!("{base}\\{rest}"),
        None => base.to_owned(),
    };
    if let Some(target) = doc.file_imports().get(first) {
        return join(target.trim_start_matches('\\'));
    }
    let short = declaring_class
        .rsplit('\\')
        .next()
        .unwrap_or(declaring_class);
    match namespace_of_class(&doc.program().stmts, short, "") {
        Some(ns) if !ns.is_empty() => format!("{ns}\\{name}"),
        _ => name.to_owned(),
    }
}

/// False when `class_name` is namespace-qualified and `doc` declares a class
/// of that short name in a different namespace. Bare names always match.
fn declared_in_namespace_of(doc: &ParsedDoc, class_name: &str) -> bool {
    let Some((ns, short)) = class_name.trim_start_matches('\\').rsplit_once('\\') else {
        return true;
    };
    namespace_of_class(&doc.program().stmts, short, "")
        .is_none_or(|declared| declared.eq_ignore_ascii_case(ns))
}

fn namespace_of_class(stmts: &[Stmt<'_, '_>], short: &str, ns_prefix: &str) -> Option<String> {
    let mut current_ns = ns_prefix.to_owned();
    for stmt in stmts {
        let declared = match &stmt.kind {
            StmtKind::Class(c) => c.name.as_ref().is_some_and(|n| *n == short),
            StmtKind::Interface(i) => i.name == short,
            StmtKind::Trait(t) => t.name == short,
            StmtKind::Enum(e) => e.name == short,
            StmtKind::Namespace(ns) => {
                let ns_name = ns
                    .name
                    .as_ref()
                    .map(|n| n.to_string_repr().to_string())
                    .unwrap_or_default();
                match &ns.body {
                    NamespaceBody::Braced(inner) => {
                        if let found @ Some(_) = namespace_of_class(&inner.stmts, short, &ns_name) {
                            return found;
                        }
                    }
                    NamespaceBody::Simple => current_ns = ns_name,
                    _ => {}
                }
                false
            }
            _ => false,
        };
        if declared {
            return Some(current_ns);
        }
    }
    None
}

/// `Some(true)` for private, `Some(false)` for protected, `None` for public.
fn restriction(visibility: Option<Visibility>) -> Option<bool> {
    match visibility {
        Some(Visibility::Private) => Some(true),
        Some(Visibility::Protected) => Some(false),
        _ => None,
    }
}

fn push_method(out: &mut ClassMembers, m: &php_ast::MethodDecl<'_, '_>) {
    out.methods.push((
        m.name.to_string(),
        m.modifiers.is_static,
        !m.params.is_empty(),
    ));
    if let Some(private) = restriction(m.modifiers.visibility) {
        out.restricted_methods.push((m.name.to_string(), private));
    }
    if let Some(return_type_hint) = &m.return_type {
        out.method_return_types.push((
            m.name.to_string(),
            crate::document::ast::format_type_hint(return_type_hint),
        ));
    }
}

fn push_property(out: &mut ClassMembers, p: &php_ast::PropertyDecl<'_, '_>) {
    out.properties
        .push((p.name.to_string(), p.modifiers.is_static));
    if let Some(private) = restriction(p.modifiers.visibility) {
        out.restricted_properties
            .push((p.name.to_string(), private));
    }
}

fn push_const(out: &mut ClassMembers, c: &php_ast::ClassConstDecl<'_, '_>) {
    out.constants.push(c.name.to_string());
    if let Some(private) = restriction(c.modifiers.visibility) {
        out.restricted_constants.push((c.name.to_string(), private));
    }
}

fn collect_members_stmts(
    source: &str,
    stmts: &[Stmt<'_, '_>],
    class_name: &str,
    out: &mut ClassMembers,
) -> Option<String> {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(c)
                if c.name.as_ref().map(|n| n.to_string()) == Some(class_name.to_string()) =>
            {
                out.found = true;
                // A `readonly class` makes every property readonly even when
                // the property itself carries no `readonly` keyword of its own.
                let class_is_readonly = c.modifiers.is_readonly;
                // Check docblock for @property and @method tags
                if let Some(raw) = docblock_before(source, stmt.span.start) {
                    let db = parse_docblock(&raw);
                    for prop in &db.properties {
                        out.properties.push((prop.name.clone(), false));
                    }
                    for method in &db.methods {
                        out.methods.push((
                            method.name.clone(),
                            method.is_static,
                            !method.params.is_empty(),
                        ));
                        if !method.return_type.is_empty() {
                            out.method_return_types
                                .push((method.name.clone(), method.return_type.clone()));
                        }
                    }
                    out.doc_methods.extend(db.methods);
                    out.mixins.extend(db.mixins);
                }
                for member in c.body.members.iter() {
                    match &member.kind {
                        ClassMemberKind::Method(m) => {
                            push_method(out, m);
                            if m.name == "__construct" {
                                for p in m.params.iter() {
                                    if p.modifiers.visibility.is_some() {
                                        out.properties.push((p.name.to_string(), false));
                                        if let Some(private) = restriction(p.modifiers.visibility) {
                                            out.restricted_properties
                                                .push((p.name.to_string(), private));
                                        }
                                        if p.modifiers.is_readonly || class_is_readonly {
                                            out.readonly_properties.push(p.name.to_string());
                                        }
                                    }
                                }
                            }
                        }
                        ClassMemberKind::Property(p) => {
                            push_property(out, p);
                            if p.modifiers.is_readonly || class_is_readonly {
                                out.readonly_properties.push(p.name.to_string());
                            }
                        }
                        ClassMemberKind::ClassConst(c) => push_const(out, c),
                        ClassMemberKind::TraitUse(t) => {
                            for name in t.traits.iter() {
                                out.trait_uses.push(name.to_string_repr().to_string());
                            }
                        }
                        _ => {}
                    }
                }
                return c.extends.as_ref().map(|n| n.to_string_repr().to_string());
            }
            StmtKind::Enum(e) if e.name == class_name => {
                out.found = true;
                let is_backed = e.scalar_type.is_some();
                out.properties.push(("name".to_string(), false));
                if is_backed {
                    out.properties.push(("value".to_string(), false));
                }
                out.methods.push(("cases".to_string(), true, false));
                if is_backed {
                    out.methods.push(("from".to_string(), true, true));
                    out.methods.push(("tryFrom".to_string(), true, true));
                }
                for member in e.body.members.iter() {
                    match &member.kind {
                        EnumMemberKind::Case(c) => {
                            out.constants.push(c.name.to_string());
                        }
                        EnumMemberKind::Method(m) => push_method(out, m),
                        EnumMemberKind::ClassConst(c) => push_const(out, c),
                        _ => {}
                    }
                }
                return None; // enums have no parent class
            }
            StmtKind::Interface(i) if i.name == class_name => {
                out.found = true;
                for member in i.body.members.iter() {
                    match &member.kind {
                        ClassMemberKind::Method(m) => push_method(out, m),
                        ClassMemberKind::Property(p) => push_property(out, p),
                        ClassMemberKind::ClassConst(c) => push_const(out, c),
                        ClassMemberKind::TraitUse(_) => {}
                        _ => {}
                    }
                }
                for parent in i.extends.iter() {
                    out.trait_uses.push(parent.to_string_repr().to_string());
                }
                return None;
            }
            StmtKind::Trait(t) if t.name == class_name => {
                out.found = true;
                for member in t.body.members.iter() {
                    match &member.kind {
                        ClassMemberKind::Method(m) => push_method(out, m),
                        ClassMemberKind::Property(p) => push_property(out, p),
                        ClassMemberKind::ClassConst(c) => push_const(out, c),
                        ClassMemberKind::TraitUse(t) => {
                            for name in t.traits.iter() {
                                out.trait_uses.push(name.to_string_repr().to_string());
                            }
                        }
                        _ => {}
                    }
                }
                return None; // traits have no parent
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body {
                    let result = collect_members_stmts(source, &inner.stmts, class_name, out);
                    if result.is_some() {
                        return result;
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// Return the `@mixin` class names declared in `class_name`'s docblock.
pub fn mixin_classes_of(doc: &ParsedDoc, class_name: &str) -> Vec<String> {
    let source = doc.source();
    let mut mixins = mixin_classes_in_stmts(source, &doc.program().stmts, class_name);
    if is_eloquent_model(class_name) || is_eloquent_model_or_short(class_name, Some(doc)) {
        let builder = "Illuminate\\Database\\Eloquent\\Builder".to_string();
        if !mixins.contains(&builder) {
            mixins.push(builder);
        }
    }
    mixins
}

pub fn is_eloquent_model(name: &str) -> bool {
    let trimmed = name.trim_start_matches('\\');
    trimmed.eq_ignore_ascii_case("Illuminate\\Database\\Eloquent\\Model")
}

pub fn is_eloquent_model_or_short(name: &str, doc: Option<&ParsedDoc>) -> bool {
    let trimmed = name.trim_start_matches('\\');
    if trimmed.eq_ignore_ascii_case("Illuminate\\Database\\Eloquent\\Model") {
        return true;
    }
    if trimmed.eq_ignore_ascii_case("Model") {
        if let Some(d) = doc {
            if namespace_of_class(&d.program().stmts, "Model", "")
                .map(|ns| ns.eq_ignore_ascii_case("Illuminate\\Database\\Eloquent"))
                .unwrap_or(false)
            {
                return true;
            }
        }
    }
    false
}

pub fn extract_builder_class_from_return_type(return_type: &str) -> Option<String> {
    let mut cleaned = return_type.trim();
    if cleaned.starts_with('?') {
        cleaned = &cleaned[1..];
    }
    if let Some(idx) = cleaned.find('<') {
        cleaned = &cleaned[..idx];
    }
    let cleaned = cleaned.trim().trim_start_matches('\\');
    if cleaned.is_empty()
        || matches!(
            cleaned.to_ascii_lowercase().as_str(),
            "void"
                | "never"
                | "null"
                | "int"
                | "integer"
                | "float"
                | "double"
                | "string"
                | "bool"
                | "boolean"
                | "array"
                | "iterable"
                | "callable"
                | "object"
                | "mixed"
                | "self"
                | "static"
                | "$this"
        )
    {
        None
    } else {
        Some(cleaned.to_string())
    }
}

fn mixin_classes_in_stmts(source: &str, stmts: &[Stmt<'_, '_>], class_name: &str) -> Vec<String> {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(c)
                if c.name.as_ref().map(|n| n.to_string()) == Some(class_name.to_string()) =>
            {
                if let Some(raw) = docblock_before(source, stmt.span.start) {
                    return parse_docblock(&raw).mixins;
                }
                return vec![];
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body {
                    let found = mixin_classes_in_stmts(source, &inner.stmts, class_name);
                    if !found.is_empty() {
                        return found;
                    }
                }
            }
            _ => {}
        }
    }
    vec![]
}

/// Return the name of the class whose body contains `position`, or `None`.
pub fn enclosing_class_at(_source: &str, doc: &ParsedDoc, position: Position) -> Option<String> {
    let sv = doc.view();
    enclosing_class_in_stmts(sv, &doc.program().stmts, position)
}

/// Like [`enclosing_class_at`] but returns the fully-qualified name
/// (`"Ns\\ClassName"`) when the class lives inside a namespace.
/// Used by the `__construct` call-site path so that `construct_references`
/// can apply namespace-level filtering and avoid matching a same-short-named
/// class in a different namespace.
pub fn enclosing_class_fqn_at(
    _source: &str,
    doc: &ParsedDoc,
    position: Position,
) -> Option<String> {
    let sv = doc.view();
    enclosing_class_fqn_in_stmts(sv, &doc.program().stmts, position, "")
}

fn enclosing_class_fqn_in_stmts(
    sv: SourceView<'_>,
    stmts: &[Stmt<'_, '_>],
    pos: Position,
    ns_prefix: &str,
) -> Option<String> {
    let mut current_ns = ns_prefix.to_owned();
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(c) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return c
                        .name
                        .map(|n| crate::text::qualify_name(&current_ns, &n.to_string()));
                }
            }
            StmtKind::Interface(i) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return Some(crate::text::qualify_name(&current_ns, &i.name.to_string()));
                }
            }
            StmtKind::Trait(t) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return Some(crate::text::qualify_name(&current_ns, &t.name.to_string()));
                }
            }
            StmtKind::Enum(e) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return Some(crate::text::qualify_name(&current_ns, &e.name.to_string()));
                }
            }
            StmtKind::Namespace(ns) => {
                let ns_name = ns
                    .name
                    .as_ref()
                    .map(|n| n.to_string_repr().to_string())
                    .unwrap_or_default();
                match &ns.body {
                    NamespaceBody::Braced(inner) => {
                        if let Some(found) =
                            enclosing_class_fqn_in_stmts(sv, &inner.stmts, pos, &ns_name)
                        {
                            return Some(found);
                        }
                    }
                    NamespaceBody::Simple => {
                        current_ns = ns_name;
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    None
}

/// Return the LSP range of the class/interface/trait/enum declaration
/// whose body contains `position`, or `None` if the cursor is outside any.
/// Used by linked-editing to scope same-name member rewrites to the
/// enclosing class instead of every class in the file.
pub fn enclosing_class_range_at(
    doc: &ParsedDoc,
    position: Position,
) -> Option<tower_lsp_server::ls_types::Range> {
    let sv = doc.view();
    enclosing_class_range_in_stmts(sv, &doc.program().stmts, position)
}

/// Return the LSP range of every class/interface/trait/enum declaration in
/// the file (recursing into braced-namespace bodies). Used by linked-editing
/// to drop highlights that fall inside an *other* class than the cursor's.
pub fn collect_all_class_ranges(doc: &ParsedDoc) -> Vec<tower_lsp_server::ls_types::Range> {
    let sv = doc.view();
    let mut out = Vec::new();
    collect_class_ranges_in_stmts(sv, &doc.program().stmts, &mut out);
    out
}

fn collect_class_ranges_in_stmts(
    sv: SourceView<'_>,
    stmts: &[Stmt<'_, '_>],
    out: &mut Vec<tower_lsp_server::ls_types::Range>,
) {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(_)
            | StmtKind::Interface(_)
            | StmtKind::Trait(_)
            | StmtKind::Enum(_) => {
                out.push(sv.range_of(stmt.span));
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body {
                    collect_class_ranges_in_stmts(sv, &inner.stmts, out);
                }
            }
            _ => {}
        }
    }
}

fn enclosing_class_range_in_stmts(
    sv: SourceView<'_>,
    stmts: &[Stmt<'_, '_>],
    pos: Position,
) -> Option<tower_lsp_server::ls_types::Range> {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(_)
            | StmtKind::Interface(_)
            | StmtKind::Trait(_)
            | StmtKind::Enum(_) => {
                let r = sv.range_of(stmt.span);
                if pos.line >= r.start.line && pos.line <= r.end.line {
                    return Some(r);
                }
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body
                    && let Some(r) = enclosing_class_range_in_stmts(sv, &inner.stmts, pos)
                {
                    return Some(r);
                }
            }
            _ => {}
        }
    }
    None
}

fn enclosing_class_in_stmts(
    sv: SourceView<'_>,
    stmts: &[Stmt<'_, '_>],
    pos: Position,
) -> Option<String> {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(c) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return c.name.map(|n| n.to_string());
                }
            }
            StmtKind::Interface(i) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return Some(i.name.to_string());
                }
            }
            StmtKind::Trait(t) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return Some(t.name.to_string());
                }
            }
            StmtKind::Enum(e) => {
                let start = sv.position_of(stmt.span.start).line;
                let end = sv.position_of(stmt.span.end).line;
                if pos.line >= start && pos.line <= end {
                    return Some(e.name.to_string());
                }
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body
                    && let Some(found) = enclosing_class_in_stmts(sv, &inner.stmts, pos)
                {
                    return Some(found);
                }
            }
            _ => {}
        }
    }
    None
}

/// Return the parameter names of the function or method named `func_name`.
pub fn params_of_function(doc: &ParsedDoc, func_name: &str) -> Vec<String> {
    let mut out = Vec::new();
    collect_params_stmts(&doc.program().stmts, func_name, &mut out);
    out
}

/// Return the parameter names of `method_name` on class `class_name`.
/// Primarily used to offer named-argument completions for attribute constructors.
pub fn params_of_method(doc: &ParsedDoc, class_name: &str, method_name: &str) -> Vec<String> {
    let short = crate::text::fqn_short_name(class_name);
    let mut out = Vec::new();
    if !declared_in_namespace_of(doc, class_name) {
        return out;
    }
    collect_method_params_stmts(&doc.program().stmts, short, method_name, &mut out);
    out
}

fn collect_method_params_stmts(
    stmts: &[php_ast::Stmt<'_, '_>],
    class_name: &str,
    method_name: &str,
    out: &mut Vec<String>,
) {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Class(c)
                if c.name.as_ref().map(|n| n.to_string()) == Some(class_name.to_string()) =>
            {
                for member in c.body.members.iter() {
                    if let ClassMemberKind::Method(m) = &member.kind
                        && m.name == method_name
                    {
                        for p in m.params.iter() {
                            out.push(p.name.to_string());
                        }
                        return;
                    }
                }
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body {
                    collect_method_params_stmts(&inner.stmts, class_name, method_name, out);
                }
            }
            _ => {}
        }
    }
}

fn collect_params_stmts(stmts: &[Stmt<'_, '_>], func_name: &str, out: &mut Vec<String>) {
    for stmt in stmts {
        match &stmt.kind {
            StmtKind::Function(f) if f.name == func_name => {
                for p in f.params.iter() {
                    out.push(p.name.to_string());
                }
                return;
            }
            StmtKind::Class(c) => {
                for member in c.body.members.iter() {
                    if let ClassMemberKind::Method(m) = &member.kind
                        && m.name == func_name
                    {
                        for p in m.params.iter() {
                            out.push(p.name.to_string());
                        }
                        return;
                    }
                }
            }
            StmtKind::Namespace(ns) => {
                if let NamespaceBody::Braced(inner) = &ns.body {
                    collect_params_stmts(&inner.stmts, func_name, out);
                }
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedMethodInfo {
    pub name: String,
    pub is_static: bool,
    pub is_virtual: bool,
    pub return_type: Option<String>,
    pub declaring_class: String,
    pub mixin_target: Option<String>,
    pub params: Vec<String>,
    pub doc_comment: Option<String>,
    pub location: Option<Location>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct ResolvedPropertyInfo {
    pub name: String,
    pub is_static: bool,
    pub type_str: Option<String>,
    pub declaring_class: String,
    pub mixin_target: Option<String>,
    pub modifiers: String,
    pub docblock: Option<crate::lang::docblock::Docblock>,
    pub location: Option<Location>,
}

enum ClassMethodSearchResult {
    Found(ResolvedMethodInfo),
    ClassDetails {
        parent_class_name: Option<String>,
        trait_names: Vec<String>,
        mixin_names: Vec<String>,
    },
    ClassMissing,
}

enum ClassPropertySearchResult {
    Found(ResolvedPropertyInfo),
    ClassDetails {
        parent_class_name: Option<String>,
        trait_names: Vec<String>,
        mixin_names: Vec<String>,
    },
    ClassMissing,
}

fn format_doc_method_parameter(param: &crate::lang::docblock::DocMethodParam) -> String {
    let mut parameter_string = String::new();
    if !param.type_hint.is_empty() {
        parameter_string.push_str(&param.type_hint);
        parameter_string.push(' ');
    }
    if param.is_byref {
        parameter_string.push('&');
    }
    if param.is_variadic {
        parameter_string.push_str("...");
    }
    if !param.name.starts_with('$') {
        parameter_string.push('$');
    }
    parameter_string.push_str(&param.name);
    parameter_string
}

fn format_ast_parameter(param: &php_ast::Param<'_, '_>) -> String {
    let mut parameter_string = String::new();
    if let Some(type_hint) = &param.type_hint {
        parameter_string.push_str(&crate::document::ast::format_type_hint(type_hint));
        parameter_string.push(' ');
    }
    if param.by_ref {
        parameter_string.push('&');
    }
    if param.variadic {
        parameter_string.push_str("...");
    }
    parameter_string.push('$');
    parameter_string.push_str(param.name.or_error());
    parameter_string
}

fn find_doc_method_range(
    source_view: SourceView<'_>,
    comment_text: &str,
    comment_span_start: u32,
    target_method_name: &str,
) -> Range {
    let mut search_offset = 0usize;
    while let Some(relative_tag_position) = comment_text[search_offset..].find("@method") {
        let tag_start_position = search_offset + relative_tag_position;
        let line_segment = &comment_text[tag_start_position..];
        let line_length = line_segment.find('\n').unwrap_or(line_segment.len());
        let current_line_text = &line_segment[..line_length];
        let method_call_needle = format!("{target_method_name}(");
        if let Some(relative_method_position) = current_line_text
            .to_ascii_lowercase()
            .find(&method_call_needle.to_ascii_lowercase())
        {
            let exact_byte_offset =
                comment_span_start + (tag_start_position + relative_method_position) as u32;
            let start_position = source_view.position_of(exact_byte_offset);
            let end_position = Position {
                line: start_position.line,
                character: start_position.character
                    + target_method_name.encode_utf16().count() as u32,
            };
            return Range::new(start_position, end_position);
        }
        search_offset = tag_start_position + "@method".len();
    }
    let fallback_position = source_view.position_of(comment_span_start);
    Range::new(fallback_position, fallback_position)
}

fn find_doc_property_range(
    source_view: SourceView<'_>,
    comment_text: &str,
    comment_span_start: u32,
    target_property_name: &str,
) -> Range {
    let clean_property_name = target_property_name.trim_start_matches('$');
    let mut search_offset = 0usize;
    while let Some(relative_tag_position) = comment_text[search_offset..].find("@property") {
        let tag_start_position = search_offset + relative_tag_position;
        let line_segment = &comment_text[tag_start_position..];
        let line_length = line_segment.find('\n').unwrap_or(line_segment.len());
        let current_line_text = &line_segment[..line_length];
        let property_needle = format!("${clean_property_name}");
        if let Some(relative_property_position) = current_line_text
            .to_ascii_lowercase()
            .find(&property_needle.to_ascii_lowercase())
        {
            let exact_byte_offset =
                comment_span_start + (tag_start_position + relative_property_position) as u32;
            let start_position = source_view.position_of(exact_byte_offset);
            let end_position = Position {
                line: start_position.line,
                character: start_position.character
                    + property_needle.encode_utf16().count() as u32,
            };
            return Range::new(start_position, end_position);
        }
        search_offset = tag_start_position + "@property".len();
    }
    let fallback_position = source_view.position_of(comment_span_start);
    Range::new(fallback_position, fallback_position)
}

fn scan_class_for_method_in_statements<'a>(
    source: &str,
    statements: &[Stmt<'a, 'a>],
    short_class_name: &str,
    target_method_name: &str,
    document_uri: Option<&tower_lsp_server::ls_types::Uri>,
    source_view: SourceView<'_>,
) -> ClassMethodSearchResult {
    for statement in statements {
        match &statement.kind {
            StmtKind::Class(class_declaration)
                if class_declaration.name.as_ref().map(|ident| ident.to_string())
                    == Some(short_class_name.to_string()) =>
            {
                for member in class_declaration.body.members.iter() {
                    if let ClassMemberKind::Method(method_declaration) = &member.kind
                        && method_declaration
                            .name
                            .or_error()
                            .eq_ignore_ascii_case(target_method_name)
                    {
                        let parameter_strings = method_declaration
                            .params
                            .iter()
                            .map(format_ast_parameter)
                            .collect();
                        let return_type_string = method_declaration
                            .return_type
                            .as_ref()
                            .map(|type_hint| crate::document::ast::format_type_hint(type_hint));
                        let name_range = source_view.name_range_in_span(
                            method_declaration.name.or_error(),
                            member.span,
                        );
                        let declaration_location = document_uri.cloned().map(|uri| Location {
                            uri,
                            range: name_range,
                        });
                        let doc_comment = docblock_before(source, member.span.start)
                            .map(|raw| parse_docblock(&raw).to_markdown());
                        return ClassMethodSearchResult::Found(ResolvedMethodInfo {
                            name: method_declaration.name.to_string(),
                            is_static: method_declaration.modifiers.is_static,
                            is_virtual: false,
                            return_type: return_type_string,
                            declaring_class: short_class_name.to_string(),
                            mixin_target: None,
                            params: parameter_strings,
                            doc_comment,
                            location: declaration_location,
                        });
                    }
                }
                let parent_class_name = class_declaration
                    .extends
                    .as_ref()
                    .map(|ident| ident.to_string_repr().to_string());
                let mut trait_names = Vec::new();
                for member in class_declaration.body.members.iter() {
                    if let ClassMemberKind::TraitUse(trait_use) = &member.kind {
                        for trait_ident in trait_use.traits.iter() {
                            trait_names.push(trait_ident.to_string_repr().to_string());
                        }
                    }
                }
                let mut mixin_names = Vec::new();
                if let Some(raw_docblock) = docblock_before(source, statement.span.start) {
                    let parsed_docblock = parse_docblock(&raw_docblock);
                    if let Some(doc_method) = parsed_docblock
                        .methods
                        .into_iter()
                        .find(|method| method.name.eq_ignore_ascii_case(target_method_name))
                    {
                        let parameter_strings = doc_method
                            .params
                            .iter()
                            .map(format_doc_method_parameter)
                            .collect();
                        let return_type_string = if doc_method.return_type.is_empty() {
                            None
                        } else {
                            Some(doc_method.return_type)
                        };
                        let method_range = find_doc_method_range(
                            source_view,
                            &raw_docblock,
                            statement.span.start,
                            target_method_name,
                        );
                        let declaration_location = document_uri.cloned().map(|uri| Location {
                            uri,
                            range: method_range,
                        });
                        return ClassMethodSearchResult::Found(ResolvedMethodInfo {
                            name: doc_method.name,
                            is_static: doc_method.is_static,
                            is_virtual: true,
                            return_type: return_type_string,
                            declaring_class: short_class_name.to_string(),
                            mixin_target: None,
                            params: parameter_strings,
                            doc_comment: None,
                            location: declaration_location,
                        });
                    }
                    mixin_names = parsed_docblock.mixins;
                }
                if is_eloquent_model(short_class_name) {
                    let builder = "Illuminate\\Database\\Eloquent\\Builder".to_string();
                    if !mixin_names.contains(&builder) {
                        mixin_names.push(builder);
                    }
                }
                return ClassMethodSearchResult::ClassDetails {
                    parent_class_name,
                    trait_names,
                    mixin_names,
                };
            }
            StmtKind::Trait(trait_declaration) if trait_declaration.name == short_class_name => {
                for member in trait_declaration.body.members.iter() {
                    if let ClassMemberKind::Method(method_declaration) = &member.kind
                        && method_declaration
                            .name
                            .or_error()
                            .eq_ignore_ascii_case(target_method_name)
                    {
                        let parameter_strings = method_declaration
                            .params
                            .iter()
                            .map(format_ast_parameter)
                            .collect();
                        let return_type_string = method_declaration
                            .return_type
                            .as_ref()
                            .map(|type_hint| crate::document::ast::format_type_hint(type_hint));
                        let name_range = source_view.name_range_in_span(
                            method_declaration.name.or_error(),
                            member.span,
                        );
                        let declaration_location = document_uri.cloned().map(|uri| Location {
                            uri,
                            range: name_range,
                        });
                        let doc_comment = docblock_before(source, member.span.start)
                            .map(|raw| parse_docblock(&raw).to_markdown());
                        return ClassMethodSearchResult::Found(ResolvedMethodInfo {
                            name: method_declaration.name.to_string(),
                            is_static: method_declaration.modifiers.is_static,
                            is_virtual: false,
                            return_type: return_type_string,
                            declaring_class: short_class_name.to_string(),
                            mixin_target: None,
                            params: parameter_strings,
                            doc_comment,
                            location: declaration_location,
                        });
                    }
                }
                let mut trait_names = Vec::new();
                for member in trait_declaration.body.members.iter() {
                    if let ClassMemberKind::TraitUse(trait_use) = &member.kind {
                        for trait_ident in trait_use.traits.iter() {
                            trait_names.push(trait_ident.to_string_repr().to_string());
                        }
                    }
                }
                return ClassMethodSearchResult::ClassDetails {
                    parent_class_name: None,
                    trait_names,
                    mixin_names: Vec::new(),
                };
            }
            StmtKind::Interface(interface_declaration)
                if interface_declaration.name == short_class_name =>
            {
                for member in interface_declaration.body.members.iter() {
                    if let ClassMemberKind::Method(method_declaration) = &member.kind
                        && method_declaration
                            .name
                            .or_error()
                            .eq_ignore_ascii_case(target_method_name)
                    {
                        let parameter_strings = method_declaration
                            .params
                            .iter()
                            .map(format_ast_parameter)
                            .collect();
                        let return_type_string = method_declaration
                            .return_type
                            .as_ref()
                            .map(|type_hint| crate::document::ast::format_type_hint(type_hint));
                        let name_range = source_view.name_range_in_span(
                            method_declaration.name.or_error(),
                            member.span,
                        );
                        let declaration_location = document_uri.cloned().map(|uri| Location {
                            uri,
                            range: name_range,
                        });
                        return ClassMethodSearchResult::Found(ResolvedMethodInfo {
                            name: method_declaration.name.to_string(),
                            is_static: method_declaration.modifiers.is_static,
                            is_virtual: false,
                            return_type: return_type_string,
                            declaring_class: short_class_name.to_string(),
                            mixin_target: None,
                            params: parameter_strings,
                            doc_comment: None,
                            location: declaration_location,
                        });
                    }
                }
                let parent_interfaces: Vec<String> = interface_declaration
                    .extends
                    .iter()
                    .map(|ident| ident.to_string_repr().to_string())
                    .collect();
                return ClassMethodSearchResult::ClassDetails {
                    parent_class_name: None,
                    trait_names: parent_interfaces,
                    mixin_names: Vec::new(),
                };
            }
            StmtKind::Namespace(namespace_statement) => {
                if let NamespaceBody::Braced(inner) = &namespace_statement.body {
                    let recursive_result = scan_class_for_method_in_statements(
                        source,
                        &inner.stmts,
                        short_class_name,
                        target_method_name,
                        document_uri,
                        source_view,
                    );
                    if !matches!(recursive_result, ClassMethodSearchResult::ClassMissing) {
                        return recursive_result;
                    }
                }
            }
            _ => {}
        }
    }
    ClassMethodSearchResult::ClassMissing
}

fn scan_class_for_property_in_statements<'a>(
    source: &str,
    statements: &[Stmt<'a, 'a>],
    short_class_name: &str,
    target_property_name: &str,
    document_uri: Option<&tower_lsp_server::ls_types::Uri>,
    source_view: SourceView<'_>,
) -> ClassPropertySearchResult {
    let clean_property_name = target_property_name.trim_start_matches('$');
    for statement in statements {
        match &statement.kind {
            StmtKind::Class(class_declaration)
                if class_declaration.name.as_ref().map(|ident| ident.to_string())
                    == Some(short_class_name.to_string()) =>
            {
                let class_is_readonly = class_declaration.modifiers.is_readonly;
                for member in class_declaration.body.members.iter() {
                    match &member.kind {
                        ClassMemberKind::Property(property_declaration)
                            if property_declaration.name == clean_property_name =>
                        {
                            let is_readonly_property =
                                property_declaration.modifiers.is_readonly || class_is_readonly;
                            let visibility_string = match property_declaration.modifiers.visibility
                            {
                                Some(Visibility::Private) => "private ",
                                Some(Visibility::Protected) => "protected ",
                                _ => "public ",
                            };
                            let static_string =
                                if property_declaration.modifiers.is_static { "static " } else { "" };
                            let readonly_string =
                                if is_readonly_property { "readonly " } else { "" };
                            let modifiers =
                                format!("{visibility_string}{static_string}{readonly_string}");
                            let type_str = property_declaration
                                .type_hint
                                .as_ref()
                                .map(|type_hint| crate::document::ast::format_type_hint(type_hint));
                            let name_range = source_view.name_range_in_span(
                                property_declaration.name.or_error(),
                                member.span,
                            );
                            let declaration_location = document_uri.cloned().map(|uri| Location {
                                uri,
                                range: name_range,
                            });
                            let docblock = docblock_before(source, member.span.start)
                                .map(|raw| parse_docblock(&raw));
                            return ClassPropertySearchResult::Found(ResolvedPropertyInfo {
                                name: clean_property_name.to_string(),
                                is_static: property_declaration.modifiers.is_static,
                                type_str,
                                declaring_class: short_class_name.to_string(),
                                mixin_target: None,
                                modifiers,
                                docblock,
                                location: declaration_location,
                            });
                        }
                        ClassMemberKind::Method(method_declaration)
                            if method_declaration.name == "__construct" =>
                        {
                            for param in method_declaration.params.iter() {
                                if param.name == clean_property_name
                                    && param.modifiers.visibility.is_some()
                                {
                                    let is_readonly_property =
                                        param.modifiers.is_readonly || class_is_readonly;
                                    let visibility_string = match param.modifiers.visibility {
                                        Some(Visibility::Private) => "private ",
                                        Some(Visibility::Protected) => "protected ",
                                        _ => "public ",
                                    };
                                    let readonly_string =
                                        if is_readonly_property { "readonly " } else { "" };
                                    let modifiers = format!("{visibility_string}{readonly_string}");
                                    let type_str = param
                                        .type_hint
                                        .as_ref()
                                        .map(|type_hint| crate::document::ast::format_type_hint(type_hint));
                                    let name_range = source_view.name_range_in_span(
                                        param.name.or_error(),
                                        member.span,
                                    );
                                    let declaration_location = document_uri.cloned().map(|uri| Location {
                                        uri,
                                        range: name_range,
                                    });
                                    return ClassPropertySearchResult::Found(ResolvedPropertyInfo {
                                        name: clean_property_name.to_string(),
                                        is_static: false,
                                        type_str,
                                        declaring_class: short_class_name.to_string(),
                                        mixin_target: None,
                                        modifiers,
                                        docblock: None,
                                        location: declaration_location,
                                    });
                                }
                            }
                        }
                        _ => {}
                    }
                }
                let parent_class_name = class_declaration
                    .extends
                    .as_ref()
                    .map(|ident| ident.to_string_repr().to_string());
                let mut trait_names = Vec::new();
                for member in class_declaration.body.members.iter() {
                    if let ClassMemberKind::TraitUse(trait_use) = &member.kind {
                        for trait_ident in trait_use.traits.iter() {
                            trait_names.push(trait_ident.to_string_repr().to_string());
                        }
                    }
                }
                let mut mixin_names = Vec::new();
                if let Some(raw_docblock) = docblock_before(source, statement.span.start) {
                    let parsed_docblock = parse_docblock(&raw_docblock);
                    if let Some(doc_property) = parsed_docblock
                        .properties
                        .into_iter()
                        .find(|prop| prop.name.trim_start_matches('$').eq_ignore_ascii_case(clean_property_name))
                    {
                        let property_range = find_doc_property_range(
                            source_view,
                            &raw_docblock,
                            statement.span.start,
                            clean_property_name,
                        );
                        let declaration_location = document_uri.cloned().map(|uri| Location {
                            uri,
                            range: property_range,
                        });
                        return ClassPropertySearchResult::Found(ResolvedPropertyInfo {
                            name: clean_property_name.to_string(),
                            is_static: false,
                            type_str: if doc_property.type_hint.is_empty() { None } else { Some(doc_property.type_hint) },
                            declaring_class: short_class_name.to_string(),
                            mixin_target: None,
                            modifiers: "public ".to_string(),
                            docblock: None,
                            location: declaration_location,
                        });
                    }
                    mixin_names = parsed_docblock.mixins;
                }
                if is_eloquent_model(short_class_name) {
                    let builder = "Illuminate\\Database\\Eloquent\\Builder".to_string();
                    if !mixin_names.contains(&builder) {
                        mixin_names.push(builder);
                    }
                }
                return ClassPropertySearchResult::ClassDetails {
                    parent_class_name,
                    trait_names,
                    mixin_names,
                };
            }
            StmtKind::Namespace(namespace_statement) => {
                if let NamespaceBody::Braced(inner) = &namespace_statement.body {
                    let recursive_result = scan_class_for_property_in_statements(
                        source,
                        &inner.stmts,
                        short_class_name,
                        target_property_name,
                        document_uri,
                        source_view,
                    );
                    if !matches!(recursive_result, ClassPropertySearchResult::ClassMissing) {
                        return recursive_result;
                    }
                }
            }
            _ => {}
        }
    }
    ClassPropertySearchResult::ClassMissing
}

pub fn find_method_in_class_hierarchy(
    document: &ParsedDoc,
    other_documents: &[Arc<ParsedDoc>],
    find_class_document: Option<crate::completion::ClassDocLookup<'_>>,
    session: Option<&crate::document::document_store::DocumentStore>,
    target_class_name: &str,
    target_method_name: &str,
) -> Option<ResolvedMethodInfo> {
    let mut class_queue: Vec<(String, Option<String>)> =
        vec![(target_class_name.trim_start_matches('\\').to_string(), None)];
    let mut visited_classes: HashSet<String> = HashSet::new();

    while let Some((current_class_name, current_mixin_target)) = class_queue.pop() {
        let normalized_class_name = current_class_name.trim_start_matches('\\').to_string();
        if !visited_classes.insert(normalized_class_name.clone()) {
            continue;
        }
        let short_class_name = crate::text::fqn_short_name(&normalized_class_name);

        if let Some(class_like) =
            session.and_then(|store| store.find_class_like(&normalized_class_name))
        {
            for method in class_like.own_methods().values() {
                if method.name.eq_ignore_ascii_case(target_method_name) {
                    let parameter_strings: Vec<String> = method
                        .params
                        .iter()
                        .map(|param| {
                            let type_string = param.ty.as_ref().map(ToString::to_string).unwrap_or_default();
                            let param_name = if param.name.as_ref().starts_with('$') {
                                param.name.to_string()
                            } else {
                                format!("${}", param.name)
                            };
                            if type_string.is_empty() {
                                param_name
                            } else {
                                format!("{type_string} {param_name}")
                            }
                        })
                        .collect();
                    let return_type_string = method
                        .return_type
                        .as_deref()
                        .or(method.inferred_return_type.as_deref())
                        .map(ToString::to_string);
                    let location = method.location.as_ref().and_then(|method_loc| {
                        let file_uri = method_loc.file.parse::<tower_lsp_server::ls_types::Uri>().ok()?;
                        let line_number = method_loc.line.saturating_sub(1);
                        let (start_character, end_character) = session
                            .and_then(|store| store.get_doc_salsa(&file_uri))
                            .and_then(|doc| {
                                let line = doc.source().lines().nth(line_number as usize)?;
                                let col = line.find(method.name.as_ref())?;
                                let utf16_col = crate::text::byte_to_utf16(line, col);
                                let utf16_len = method.name.encode_utf16().count() as u32;
                                Some((utf16_col, utf16_col + utf16_len))
                            })
                            .unwrap_or_else(|| {
                                let start = method_loc.col_start as u32;
                                let end = start + method.name.encode_utf16().count() as u32;
                                (start, end)
                            });
                        Some(Location {
                            uri: file_uri,
                            range: Range::new(
                                Position::new(line_number, start_character),
                                Position::new(line_number, end_character),
                            ),
                        })
                    });
                    return Some(ResolvedMethodInfo {
                        name: method.name.to_string(),
                        is_static: method.is_static,
                        is_virtual: method.is_virtual,
                        return_type: return_type_string,
                        declaring_class: class_like.fqcn().to_string(),
                        mixin_target: current_mixin_target,
                        params: parameter_strings,
                        doc_comment: method.docstring.as_deref().map(ToString::to_string),
                        location,
                    });
                }
            }
            for ancestor_class_name in class_like.ancestor_fqcns().into_iter().rev() {
                class_queue.push((ancestor_class_name.to_string(), current_mixin_target.clone()));
            }
            let mut mixins: Vec<String> = class_like.mixins().iter().map(|m| m.to_string()).collect();
            if is_eloquent_model(&normalized_class_name)
                || is_eloquent_model(class_like.fqcn().trim_start_matches('\\'))
            {
                let builder = "Illuminate\\Database\\Eloquent\\Builder";
                if !mixins.iter().any(|m| m == builder) {
                    mixins.push(builder.to_string());
                }
            }
            if let Some(query_method) = class_like.own_methods().get("query") {
                if let Some(return_type) = query_method
                    .return_type
                    .as_deref()
                    .or(query_method.inferred_return_type.as_deref())
                {
                    let type_str = return_type.to_string();
                    if let Some(builder_class) = extract_builder_class_from_return_type(&type_str) {
                        if !mixins.iter().any(|m| m == &builder_class) {
                            mixins.push(builder_class);
                        }
                    }
                }
            }
            for mixin_class_name in mixins.iter().rev() {
                class_queue.push((
                    mixin_class_name.to_string(),
                    Some(mixin_class_name.to_string()),
                ));
            }
            continue;
        }

        let fast_document = find_class_document.and_then(|lookup| lookup(&normalized_class_name));
        let defining_document = match fast_document.as_deref() {
            Some(doc_ref) => Some(doc_ref),
            None => {
                let all_documents: Vec<&ParsedDoc> = std::iter::once(document)
                    .chain(other_documents.iter().map(|d| d.as_ref()))
                    .collect();
                all_documents
                    .into_iter()
                    .find(|doc_candidate| declared_in_namespace_of(doc_candidate, &normalized_class_name))
            }
        };

        if let Some(defining_doc) = defining_document {
            match scan_class_for_method_in_statements(
                defining_doc.source(),
                &defining_doc.program().stmts,
                short_class_name,
                target_method_name,
                None,
                defining_doc.view(),
            ) {
                ClassMethodSearchResult::Found(mut resolved_method_info) => {
                    resolved_method_info.declaring_class = normalized_class_name.clone();
                    resolved_method_info.mixin_target = current_mixin_target;
                    return Some(resolved_method_info);
                }
                ClassMethodSearchResult::ClassDetails {
                    parent_class_name,
                    trait_names,
                    mut mixin_names,
                } => {
                    if is_eloquent_model(&normalized_class_name)
                        || is_eloquent_model_or_short(short_class_name, Some(defining_doc))
                    {
                        let builder = "Illuminate\\Database\\Eloquent\\Builder".to_string();
                        if !mixin_names.contains(&builder) {
                            mixin_names.push(builder);
                        }
                    }
                    if let Some(parent_class) = parent_class_name {
                        let resolved_parent =
                            resolve_class_ref(defining_doc, short_class_name, &parent_class);
                        class_queue.push((resolved_parent, current_mixin_target.clone()));
                    }
                    for trait_name in trait_names {
                        let resolved_trait =
                            resolve_class_ref(defining_doc, short_class_name, &trait_name);
                        class_queue.push((resolved_trait, current_mixin_target.clone()));
                    }
                    for mixin_name in mixin_names {
                        let resolved_mixin =
                            resolve_class_ref(defining_doc, short_class_name, &mixin_name);
                        class_queue.push((resolved_mixin.clone(), Some(resolved_mixin)));
                    }
                }
                ClassMethodSearchResult::ClassMissing => {}
            }
        }
    }
    None
}

pub fn find_property_in_class_hierarchy(
    document: &ParsedDoc,
    other_documents: &[Arc<ParsedDoc>],
    find_class_document: Option<crate::completion::ClassDocLookup<'_>>,
    session: Option<&crate::document::document_store::DocumentStore>,
    target_class_name: &str,
    target_property_name: &str,
) -> Option<ResolvedPropertyInfo> {
    let mut class_queue: Vec<(String, Option<String>)> =
        vec![(target_class_name.trim_start_matches('\\').to_string(), None)];
    let mut visited_classes: HashSet<String> = HashSet::new();

    while let Some((current_class_name, current_mixin_target)) = class_queue.pop() {
        let normalized_class_name = current_class_name.trim_start_matches('\\').to_string();
        if !visited_classes.insert(normalized_class_name.clone()) {
            continue;
        }
        let short_class_name = crate::text::fqn_short_name(&normalized_class_name);

        if let Some(class_like) =
            session.and_then(|store| store.find_class_like(&normalized_class_name))
        {
            let clean_property_name = target_property_name.trim_start_matches('$');
            for property in class_like
                .own_properties()
                .into_iter()
                .flat_map(|props| props.values())
            {
                if property.name.eq_ignore_ascii_case(clean_property_name) {
                    let type_string = property.ty.as_deref().map(ToString::to_string);
                    let modifiers = if property.is_static {
                        "public static ".to_string()
                    } else {
                        "public ".to_string()
                    };
                    return Some(ResolvedPropertyInfo {
                        name: property.name.to_string(),
                        is_static: property.is_static,
                        type_str: type_string,
                        declaring_class: class_like.fqcn().to_string(),
                        mixin_target: current_mixin_target,
                        modifiers,
                        docblock: None,
                        location: None,
                    });
                }
            }
            for ancestor_class_name in class_like.ancestor_fqcns().into_iter().rev() {
                class_queue.push((ancestor_class_name.to_string(), current_mixin_target.clone()));
            }
            let mut mixins: Vec<String> = class_like.mixins().iter().map(|m| m.to_string()).collect();
            if is_eloquent_model(&normalized_class_name)
                || is_eloquent_model(class_like.fqcn().trim_start_matches('\\'))
            {
                let builder = "Illuminate\\Database\\Eloquent\\Builder";
                if !mixins.iter().any(|m| m == builder) {
                    mixins.push(builder.to_string());
                }
            }
            if let Some(query_method) = class_like.own_methods().get("query") {
                if let Some(return_type) = query_method
                    .return_type
                    .as_deref()
                    .or(query_method.inferred_return_type.as_deref())
                {
                    let type_str = return_type.to_string();
                    if let Some(builder_class) = extract_builder_class_from_return_type(&type_str) {
                        if !mixins.iter().any(|m| m == &builder_class) {
                            mixins.push(builder_class);
                        }
                    }
                }
            }
            for mixin_class_name in mixins.iter().rev() {
                class_queue.push((
                    mixin_class_name.to_string(),
                    Some(mixin_class_name.to_string()),
                ));
            }
            continue;
        }

        let fast_document = find_class_document.and_then(|lookup| lookup(&normalized_class_name));
        let defining_document = match fast_document.as_deref() {
            Some(doc_ref) => Some(doc_ref),
            None => {
                let all_documents: Vec<&ParsedDoc> = std::iter::once(document)
                    .chain(other_documents.iter().map(|d| d.as_ref()))
                    .collect();
                all_documents
                    .into_iter()
                    .find(|doc_candidate| declared_in_namespace_of(doc_candidate, &normalized_class_name))
            }
        };

        if let Some(defining_doc) = defining_document {
            match scan_class_for_property_in_statements(
                defining_doc.source(),
                &defining_doc.program().stmts,
                short_class_name,
                target_property_name,
                None,
                defining_doc.view(),
            ) {
                ClassPropertySearchResult::Found(mut resolved_property_info) => {
                    resolved_property_info.declaring_class = normalized_class_name.clone();
                    resolved_property_info.mixin_target = current_mixin_target;
                    return Some(resolved_property_info);
                }
                ClassPropertySearchResult::ClassDetails {
                    parent_class_name,
                    trait_names,
                    mut mixin_names,
                } => {
                    if is_eloquent_model(&normalized_class_name)
                        || is_eloquent_model_or_short(short_class_name, Some(defining_doc))
                    {
                        let builder = "Illuminate\\Database\\Eloquent\\Builder".to_string();
                        if !mixin_names.contains(&builder) {
                            mixin_names.push(builder);
                        }
                    }
                    if let Some(parent_class) = parent_class_name {
                        let resolved_parent =
                            resolve_class_ref(defining_doc, short_class_name, &parent_class);
                        class_queue.push((resolved_parent, current_mixin_target.clone()));
                    }
                    for trait_name in trait_names {
                        let resolved_trait =
                            resolve_class_ref(defining_doc, short_class_name, &trait_name);
                        class_queue.push((resolved_trait, current_mixin_target.clone()));
                    }
                    for mixin_name in mixin_names {
                        let resolved_mixin =
                            resolve_class_ref(defining_doc, short_class_name, &mixin_name);
                        class_queue.push((resolved_mixin.clone(), Some(resolved_mixin)));
                    }
                }
                ClassPropertySearchResult::ClassMissing => {}
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    const OTHER_SVC: &str =
        "<?php\nnamespace Other;\nclass Svc { const B = 2; public function run(int $wrong) {} }";

    #[test]
    fn members_of_class_respects_namespace_of_qualified_name() {
        let doc = ParsedDoc::parse(OTHER_SVC.to_string());
        assert_eq!(members_of_class(&doc, "\\Other\\Svc").constants, ["B"]);
        assert!(!members_of_class(&doc, "App\\Svc").found);
        assert!(members_of_class(&doc, "Svc").found);
    }

    #[test]
    fn params_of_method_respects_namespace_of_qualified_name() {
        let doc = ParsedDoc::parse(OTHER_SVC.to_string());
        assert_eq!(params_of_method(&doc, "Other\\Svc", "run"), ["wrong"]);
        assert!(params_of_method(&doc, "App\\Svc", "run").is_empty());
    }

    #[test]
    fn parent_class_name_finds_parent() {
        let src = "<?php\nclass Base {}\nclass Child extends Base {}";
        let doc = ParsedDoc::parse(src.to_string());
        assert_eq!(parent_class_name(&doc, "Child"), Some("Base".to_string()));
    }

    #[test]
    fn parent_class_name_returns_none_for_top_level() {
        let src = "<?php\nclass Base {}";
        let doc = ParsedDoc::parse(src.to_string());
        assert!(parent_class_name(&doc, "Base").is_none());
    }

    #[test]
    fn members_of_class_includes_parent_field() {
        let src = "<?php\nclass Base {}\nclass Child extends Base {}";
        let doc = ParsedDoc::parse(src.to_string());
        let m = members_of_class(&doc, "Child");
        assert_eq!(m.parent.as_deref(), Some("Base"));
    }

    #[test]
    fn members_of_class_finds_methods() {
        let src = "<?php\nclass Calc { public function add() {} public function sub() {} }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Calc");
        let names: Vec<&str> = members.methods.iter().map(|(n, _, _)| n.as_str()).collect();
        assert!(names.contains(&"add"), "missing 'add'");
        assert!(names.contains(&"sub"), "missing 'sub'");
    }

    #[test]
    fn members_of_class_tracks_has_params_per_method() {
        let src = "<?php\nclass Calc { public function reset() {} public function add(int $x) {} }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Calc");
        let has_params = |name: &str| {
            members
                .methods
                .iter()
                .find(|(n, _, _)| n == name)
                .map(|(_, _, p)| *p)
        };
        assert_eq!(has_params("reset"), Some(false));
        assert_eq!(has_params("add"), Some(true));
    }

    #[test]
    fn members_of_unknown_class_is_empty() {
        let src = "<?php\nclass Calc { public function add() {} }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Unknown");
        assert!(members.methods.is_empty());
    }

    #[test]
    fn constructor_promoted_params_appear_as_properties() {
        let src = "<?php\nclass Point {\n    public function __construct(\n        public float $x,\n        public float $y,\n    ) {}\n}";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Point");
        let prop_names: Vec<&str> = members.properties.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            prop_names.contains(&"x"),
            "promoted param x should be a property"
        );
        assert!(
            prop_names.contains(&"y"),
            "promoted param y should be a property"
        );
    }

    #[test]
    fn promoted_readonly_params_appear_in_readonly_properties() {
        let src = "<?php\nclass User {\n    public function __construct(\n        public readonly string $name,\n        public int $age,\n    ) {}\n}";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "User");
        let prop_names: Vec<&str> = members.properties.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            prop_names.contains(&"name"),
            "promoted param name should be a property"
        );
        assert!(
            prop_names.contains(&"age"),
            "promoted param age should be a property"
        );
        assert!(
            members.readonly_properties.contains(&"name".to_string()),
            "readonly promoted param name should be in readonly_properties"
        );
        assert!(
            !members.readonly_properties.contains(&"age".to_string()),
            "non-readonly promoted param age should not be in readonly_properties"
        );
    }

    #[test]
    fn enum_instance_members_include_name() {
        let src = "<?php\nenum Status { case Active; case Inactive; }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Status");
        let prop_names: Vec<&str> = members.properties.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            prop_names.contains(&"name"),
            "pure enum should expose ->name"
        );
        assert!(
            !prop_names.contains(&"value"),
            "pure enum should not expose ->value"
        );
    }

    #[test]
    fn backed_enum_exposes_value_and_factory_methods() {
        let src = "<?php\nenum Color: string { case Red = 'red'; }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Color");
        let prop_names: Vec<&str> = members.properties.iter().map(|(n, _)| n.as_str()).collect();
        let method_names: Vec<&str> = members.methods.iter().map(|(n, _, _)| n.as_str()).collect();
        assert!(
            prop_names.contains(&"value"),
            "backed enum should expose ->value"
        );
        assert!(
            method_names.contains(&"from"),
            "backed enum should have ::from()"
        );
        assert!(
            method_names.contains(&"tryFrom"),
            "backed enum should have ::tryFrom()"
        );
        assert!(
            method_names.contains(&"cases"),
            "enum should have ::cases()"
        );
    }

    #[test]
    fn enum_cases_appear_as_constants() {
        let src = "<?php\nenum Status { case Active; case Inactive; }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Status");
        assert!(members.constants.contains(&"Active".to_string()));
        assert!(members.constants.contains(&"Inactive".to_string()));
    }

    #[test]
    fn trait_members_are_collected() {
        let src = "<?php\ntrait Logging { public function log() {} public string $logFile; }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Logging");
        let method_names: Vec<&str> = members.methods.iter().map(|(n, _, _)| n.as_str()).collect();
        let prop_names: Vec<&str> = members.properties.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            method_names.contains(&"log"),
            "trait method log should be collected"
        );
        assert!(
            prop_names.contains(&"logFile"),
            "trait property logFile should be collected"
        );
    }

    #[test]
    fn class_with_trait_use_lists_trait() {
        let src = "<?php\ntrait Logging { public function log() {} }\nclass App { use Logging; }";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "App");
        assert!(
            members.trait_uses.contains(&"Logging".to_string()),
            "should list used trait"
        );
    }

    #[test]
    fn docblock_property_appears_in_members() {
        let src =
            "<?php\n/**\n * @property string $email\n * @property-read int $id\n */\nclass User {}";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "User");
        let props: Vec<&str> = members.properties.iter().map(|(n, _)| n.as_str()).collect();
        assert!(props.contains(&"email"));
        assert!(props.contains(&"id"));
    }

    #[test]
    fn docblock_method_appears_in_members() {
        let src = "<?php\n/**\n * @method User find(int $id)\n * @method static Builder where(string $col, mixed $val)\n */\nclass Model {}";
        let doc = ParsedDoc::parse(src.to_string());
        let members = members_of_class(&doc, "Model");
        let method_names: Vec<&str> = members.methods.iter().map(|(n, _, _)| n.as_str()).collect();
        assert!(method_names.contains(&"find"));
        assert!(method_names.contains(&"where"));
        let where_static = members
            .methods
            .iter()
            .find(|(n, _, _)| n == "where")
            .map(|(_, s, _)| *s);
        assert_eq!(where_static, Some(true));
        let find_has_params = members
            .methods
            .iter()
            .find(|(n, _, _)| n == "find")
            .map(|(_, _, p)| *p);
        assert_eq!(find_has_params, Some(true));
    }
}
