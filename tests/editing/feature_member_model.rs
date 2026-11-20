use super::*;
use expect_test::expect;

/// Member lines (methods/properties/constants) of a completion rendering.
fn members(out: &str) -> String {
    out.lines()
        .filter(|l| {
            l.starts_with("Method ") || l.starts_with("Property ") || l.starts_with("Constant ")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[tokio::test]
async fn interface_receiver_completes_its_own_methods() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
interface Shape { public function area(): float; }
class Other { public function unrelated(): void {} }
function f(Shape $x) { $x->$0 }
"#,
        )
        .await;
    expect!["Method      area"].assert_eq(&members(&out));
}

#[tokio::test]
async fn interface_receiver_includes_parent_interface_methods() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
namespace App;
interface Named { public function name(): string; }
interface Shape extends Named { public function area(): float; }
function f(Shape $x) { $x->$0 }
"#,
        )
        .await;
    expect![[r#"
        Method      area
        Method      name"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn inherited_private_members_are_not_offered() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class Base {
    private $hidden;
    protected $guarded;
    private function secret(): void {}
    protected function prot(): void {}
    public function pub(): void {}
}
class Child extends Base {}
$c = new Child();
$c->$0
"#,
        )
        .await;
    expect!["Method      pub"].assert_eq(&members(&out));
}

#[tokio::test]
async fn own_private_and_protected_members_are_hidden_outside_the_class() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class X {
    private $p;
    protected $q;
    public $r;
    public function __construct() {}
    private function pm(): void {}
    protected function qm(): void {}
    public function rm(): void {}
}
$x = new X();
$x->$0
"#,
        )
        .await;
    expect![[r#"
        Property    $r
        Method      rm"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn own_private_members_are_offered_inside_the_class() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class X {
    private $p;
    protected $q;
    private function pm(): void {}
    public function run(): void { $this->$0 }
}
"#,
        )
        .await;
    expect![[r#"
        Property    $p
        Property    $q
        Method      pm
        Method      run"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn private_members_of_another_class_are_hidden_inside_a_class() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class X {
    private function pm(): void {}
    public function rm(): void {}
}
class Y {
    public function run(X $x): void { $x->$0 }
}
"#,
        )
        .await;
    expect!["Method      rm"].assert_eq(&members(&out));
}

#[tokio::test]
async fn private_static_members_are_hidden_outside_the_class() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class X {
    private const HIDDEN = 1;
    public const SHOWN = 2;
    private static function pm(): void {}
    public static function rm(): void {}
}
X::$0
"#,
        )
        .await;
    expect![[r#"
        Constant    SHOWN
        Method      rm"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn parent_static_access_offers_instance_methods() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class P {
    public $prop;
    public static $sprop;
    public function __construct() {}
    private function pm(): void {}
    protected function qm(): void {}
    public function rm(): void {}
    public static function sm(): void {}
}
class C extends P {
    public function rm(): void { parent::$0 }
}
"#,
        )
        .await;
    expect![[r#"
        Property    $sprop
        Method      __construct
        Method      qm
        Method      rm
        Method      sm"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn inherited_protected_members_are_offered_inside_a_subclass() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class Base {
    private function secret(): void {}
    protected function prot(): void {}
    public function pub(): void {}
}
class Child extends Base {
    public function run(): void { $this->$0 }
}
"#,
        )
        .await;
    expect![[r#"
        Method      prot
        Method      pub
        Method      run"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn parent_resolves_against_the_declaring_files_imports() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"//- /a/Base.php
<?php
namespace A;
class Base { public function fromA(): void {} }

//- /b/Base.php
<?php
namespace B;
class Base { public function fromB(): void {} }

//- /a/Mid.php
<?php
namespace A;
class Mid extends Base {}

//- /main.php
<?php
use B\Base;
use A\Mid;
function f(Mid $m) { $m->$0 }
"#,
        )
        .await;
    expect!["Method      fromA"].assert_eq(&members(&out));
}

#[tokio::test]
async fn namespaced_enum_gets_match_arm_completion() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
namespace App;
enum Suit { case Hearts; case Spades; }
function f(Suit $s) {
    match ($s) {
        $0
    }
}
"#,
        )
        .await;
    let arms: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("Constant    Suit::"))
        .collect();
    expect![[r#"
        Constant    Suit::Hearts
        Constant    Suit::Spades"#]]
    .assert_eq(&arms.join("\n"));
}

#[tokio::test]
async fn signature_help_scopes_method_to_receiver_class() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_signature_help(
            r#"<?php
class Logger { public function send(string $line): void {} }
class Mailer { public function send(string $to, string $body): void {} }
$mailer = new Mailer();
$mailer->send($0);
"#,
        )
        .await;
    expect!["▶ send(string $to, string $body)  @param0"].assert_eq(&out);
}

#[tokio::test]
async fn namespaced_receiver_gets_named_argument_completion() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
namespace App;
class Mailer { public function send(string $to, string $body): void {} }
function f(Mailer $m) { $m->send($0); }
"#,
        )
        .await;
    let named: Vec<&str> = out
        .lines()
        .filter(|l| l.contains("to:") || l.contains("body:"))
        .collect();
    expect!["Method      send(to:, body:) | named args"].assert_eq(&named.join("\n"));
}

#[tokio::test]
async fn imported_static_receiver_gets_named_argument_completion() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"//- /Mailer.php
<?php
namespace Lib;
class Mailer { public static function send(string $to, string $body): void {} }

//- /main.php
<?php
use Lib\Mailer;
Mailer::send($0);
"#,
        )
        .await;
    let named: Vec<&str> = out
        .lines()
        .filter(|l| l.contains("to:") || l.contains("body:"))
        .collect();
    expect!["Method      send(to:, body:) | named args"].assert_eq(&named.join("\n"));
}

#[tokio::test]
async fn docblock_property_and_method_tags_are_offered() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
/**
 * @property string $email
 * @property-read int $id
 * @method int total()
 * @method static self make()
 */
class User {}
function f(User $u) { $u->$0 }
"#,
        )
        .await;
    expect![[r#"
        Property    $email
        Property    $id
        Method      make
        Method      total"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn mixin_public_members_are_offered() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class Builder {
    public function where(): static { return $this; }
    protected function guarded(): void {}
    public static function query(): void {}
}
/** @mixin Builder */
class Model { public function save(): void {} }
function f(Model $m) { $m->$0 }
"#,
        )
        .await;
    expect![[r#"
        Method      save
        Method      where"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn private_trait_members_are_offered_inside_the_using_class() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
trait Helpers {
    private function helper(): void {}
}
class Base {
    use Helpers;
}
class Child extends Base {
    use Helpers2;
    public function run(): void { $this->$0 }
}
trait Helpers2 {
    private function own(): void {}
}
"#,
        )
        .await;
    expect![[r#"
        Method      own
        Method      run"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn interface_constants_are_offered_on_implementing_class() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
namespace App;
interface HasVersion { const VERSION = 1; }
class Release implements HasVersion { const NAME = 'x'; }
Release::$0
"#,
        )
        .await;
    expect![[r#"
        Constant    NAME
        Constant    VERSION"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn backed_enum_static_access_offers_cases_and_builtins() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
namespace App;
enum Suit: string {
    case Hearts = 'h';
    const DEFAULT = self::Hearts;
    public static function random(): self { return self::Hearts; }
}
Suit::$0
"#,
        )
        .await;
    expect![[r#"
        Constant    DEFAULT
        Constant    Hearts
        Method      cases
        Method      from
        Method      random
        Method      tryFrom"#]]
    .assert_eq(&members(&out));
}

/// Unopened PSR-4 vendor classes: traits and the grandparent of a vendor
/// parent must all contribute members.
#[tokio::test]
async fn vendor_parent_traits_and_grandparent_members_are_offered() {
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("vendor/acme/console/src");
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(
        tmp.path().join("composer.json"),
        r#"{"autoload":{"psr-4":{"Acme\\Console\\":"vendor/acme/console/src/"}}}"#,
    )
    .unwrap();
    std::fs::write(
        src.join("BaseCommand.php"),
        "<?php\nnamespace Acme\\Console;\nclass BaseCommand { public function run(): int { return 0; } }\n",
    )
    .unwrap();
    std::fs::write(
        src.join("InteractsWithIO.php"),
        "<?php\nnamespace Acme\\Console;\ntrait InteractsWithIO { public function line(): void {} }\n",
    )
    .unwrap();
    std::fs::write(
        src.join("CallsCommands.php"),
        "<?php\nnamespace Acme\\Console;\ntrait CallsCommands { protected function call(): void {} }\n",
    )
    .unwrap();
    std::fs::write(
        src.join("Command.php"),
        "<?php\nnamespace Acme\\Console;\nclass Command extends BaseCommand {\n    use InteractsWithIO, CallsCommands;\n    private function secret(): void {}\n}\n",
    )
    .unwrap();
    let caller = "<?php\nnamespace App;\nuse Acme\\Console\\Command;\nclass Sync extends Command {\n    public function handle(): void {\n        $this->\n    }\n}\n";
    std::fs::write(tmp.path().join("Sync.php"), caller).unwrap();

    let mut s = TestServer::with_root(tmp.path()).await;
    s.validate_syntax(false);
    s.wait_for_index_ready().await;
    s.open("Sync.php", caller).await;

    let (_, line, ch) = s.locate("Sync.php", "$this->", 0);
    let resp = s
        .completion("Sync.php", line, ch + "$this->".len() as u32)
        .await;
    let out = render_completion_ordered(&resp);
    expect![[r#"
        Method      call
        Method      handle
        Method      line
        Method      run"#]]
    .assert_eq(&members(&out));
}

/// Completion at `$0` triggered by `(`, the only trigger that offers named arguments.
async fn paren_completion(s: &mut TestServer, src: &str) -> String {
    let opened = s.open_fixture(src).await;
    let c = opened.cursor().clone();
    let uri = s.uri(&c.path);
    let resp = s
        .client()
        .request(
            "textDocument/completion",
            serde_json::json!({
                "textDocument": { "uri": uri },
                "position": { "line": c.line, "character": c.character },
                "context": { "triggerKind": 2, "triggerCharacter": "(" },
            }),
        )
        .await;
    render_completion(&resp)
}

#[tokio::test]
async fn inherited_method_gets_named_argument_completion() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = paren_completion(
        &mut s,
        r#"<?php
namespace App;
class Base { public function send(string $to, string $body): void {} }
class Mailer extends Base {}
function f(Mailer $m) { $m->send($0); }
"#,
    )
    .await;
    expect![[r#"
        Variable    body:
        Variable    to:"#]]
    .assert_eq(&out);
}

#[tokio::test]
async fn trait_and_mixin_methods_get_named_argument_completion() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = paren_completion(
        &mut s,
        r#"<?php
class Builder { public function where(string $column, mixed $value): static { return $this; } }
trait Logs { public function log(string $message): void {} }
/** @mixin Builder */
class Model { use Logs; }
function f(Model $m) { $m->where($0); }
"#,
    )
    .await;
    expect![[r#"
        Variable    column:
        Variable    value:"#]]
    .assert_eq(&out);

    let out = paren_completion(
        &mut s,
        r#"<?php
class Builder { public function where(string $column, mixed $value): static { return $this; } }
trait Logs { public function log(string $message): void {} }
/** @mixin Builder */
class Model { use Logs; }
function f(Model $m) { $m->log($0); }
"#,
    )
    .await;
    expect!["Variable    message:"].assert_eq(&out);
}

#[tokio::test]
async fn inherited_static_method_gets_named_argument_completion() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = paren_completion(
        &mut s,
        r#"<?php
namespace App;
class Factory { public static function make(string $name, int $size): static { return new static(); } }
class Widget extends Factory {}
Widget::make($0);
"#,
    )
    .await;
    expect![[r#"
        Variable    name:
        Variable    size:"#]]
    .assert_eq(&out);
}

/// Attribute classes usually live in unopened vendor files.
#[tokio::test]
async fn unopened_vendor_attribute_gets_constructor_named_arguments() {
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("vendor/acme/routing/src");
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(
        tmp.path().join("composer.json"),
        r#"{"autoload":{"psr-4":{"Acme\\Routing\\":"vendor/acme/routing/src/"}}}"#,
    )
    .unwrap();
    std::fs::write(
        src.join("Route.php"),
        "<?php\nnamespace Acme\\Routing;\n#[\\Attribute]\nclass Route {\n    public function __construct(string $path, array $methods = []) {}\n}\n",
    )
    .unwrap();
    let caller = "<?php\nnamespace App;\nuse Acme\\Routing\\Route;\nclass Home {\n    #[Route(\n    public function index(): void {}\n}\n";
    std::fs::write(tmp.path().join("Home.php"), caller).unwrap();

    let mut s = TestServer::with_root(tmp.path()).await;
    s.validate_syntax(false);
    s.wait_for_index_ready().await;
    s.open("Home.php", caller).await;

    let (_, line, ch) = s.locate("Home.php", "#[Route(", 0);
    let uri = s.uri("Home.php");
    let resp = s
        .client()
        .request(
            "textDocument/completion",
            serde_json::json!({
                "textDocument": { "uri": uri },
                "position": { "line": line, "character": ch + "#[Route(".len() as u32 },
                "context": { "triggerKind": 2, "triggerCharacter": "(" },
            }),
        )
        .await;
    expect![[r#"
        Variable    methods: | #Route argument
        Variable    path: | #Route argument"#]]
    .assert_eq(&render_completion_ordered(&resp));
}

#[tokio::test]
async fn mixin_public_members_are_offered_on_static_call() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class Builder {
    public function where(): static { return $this; }
    public function get(): array { return []; }
    public static function query(): void {}
}
/** @mixin Builder */
class Model { public function save(): void {} }
Model::$0
"#,
        )
        .await;
    expect![[r#"
        Method      get
        Method      query
        Method      where"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn mixin_inherited_from_parent_class_on_static_call() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class Builder {
    public function where(): static { return $this; }
    public function first(): static { return $this; }
    public function get(): array { return []; }
}
/** @mixin Builder */
class Model {}
class User extends Model {}
User::$0
"#,
        )
        .await;
    expect![[r#"
        Method      first
        Method      get
        Method      where"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn chained_call_after_static_call_resolves_mixin_return_type() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class Builder {
    public function where(string $col, mixed $val): static { return $this; }
    public function first(): ?static { return $this; }
    public function get(): array { return []; }
    public function orderBy(string $column): static { return $this; }
}
/** @mixin Builder */
class Model {}
class User extends Model {}
User::where('id', 1)->$0
"#,
        )
        .await;
    expect![[r#"
        Method      first
        Method      get
        Method      orderBy
        Method      where"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn chained_call_multi_level_resolves_return_type() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let out = s
        .check_completion_ordered(
            r#"<?php
class Builder {
    public function where(string $col, mixed $val): static { return $this; }
    public function orderBy(string $column): static { return $this; }
    public function get(): array { return []; }
}
/** @mixin Builder */
class Model {}
class User extends Model {}
User::where('id', 1)->orderBy('name')->$0
"#,
        )
        .await;
    expect![[r#"
        Method      get
        Method      orderBy
        Method      where"#]]
    .assert_eq(&members(&out));
}

#[tokio::test]
async fn method_docblock_honoured_for_static_and_instance_calls() {
    let mut s = TestServer::new().await;
    s.validate_syntax(false);
    let static_out = s
        .check_completion_ordered(
            r#"<?php
/**
 * @method static int compute(int $x)
 * @method string format(string $pattern)
 */
class Service {}
Service::$0
"#,
        )
        .await;
    expect![[r#"
        Method      compute
        Method      format"#]]
    .assert_eq(&members(&static_out));

    let instance_out = s
        .check_completion_ordered(
            r#"<?php
/**
 * @method static int compute(int $x)
 * @method string format(string $pattern)
 */
class Service {}
function test(Service $service) {
    $service->$0
}
"#,
        )
        .await;
    expect![[r#"
        Method      compute
        Method      format"#]]
    .assert_eq(&members(&instance_out));
}

#[tokio::test]
async fn probe_case_builder_chain_indexed_from_workspace() {
    let tmp = tempfile::tempdir().unwrap();
    let app_dir = tmp.path().join("app/Models");
    let auth_dir = tmp.path().join("vendor/laravel/framework/src/Illuminate/Foundation/Auth");
    let elo_dir = tmp.path().join("vendor/laravel/framework/src/Illuminate/Database/Eloquent");
    let qry_dir = tmp.path().join("vendor/laravel/framework/src/Illuminate/Database/Query");
    std::fs::create_dir_all(&app_dir).unwrap();
    std::fs::create_dir_all(&auth_dir).unwrap();
    std::fs::create_dir_all(&elo_dir).unwrap();
    std::fs::create_dir_all(&qry_dir).unwrap();

    std::fs::write(
        tmp.path().join("composer.json"),
        r#"{"autoload":{"psr-4":{"App\\":"app/","Illuminate\\Foundation\\":"vendor/laravel/framework/src/Illuminate/Foundation/","Illuminate\\Database\\":"vendor/laravel/framework/src/Illuminate/Database/"}}}"#,
    )
    .unwrap();

    std::fs::write(
        qry_dir.join("Builder.php"),
        r#"<?php
namespace Illuminate\Database\Query;

class Builder {
    public function first($columns = ['*']) { return null; }
    public function orderBy($column, $direction = 'asc') { return $this; }
}
"#,
    )
    .unwrap();

    std::fs::write(
        elo_dir.join("Builder.php"),
        r#"<?php
namespace Illuminate\Database\Eloquent;

/**
 * @template TModel of \Illuminate\Database\Eloquent\Model
 * @mixin \Illuminate\Database\Query\Builder
 */
class Builder {
    /**
     * @param mixed $column
     * @param mixed $operator
     * @param mixed $value
     * @param string $boolean
     * @return $this
     */
    public function where($column, $operator = null, $value = null, $boolean = 'and') { return $this; }
    public function get($columns = ['*']) { return []; }
}
"#,
    )
    .unwrap();

    std::fs::write(
        elo_dir.join("Model.php"),
        r#"<?php
namespace Illuminate\Database\Eloquent;

abstract class Model {
    /**
     * @var class-string<\Illuminate\Database\Eloquent\Builder<*>>
     */
    protected static string $builder = Builder::class;

    /**
     * Begin querying the model.
     *
     * @return \Illuminate\Database\Eloquent\Builder<static>
     */
    public static function query()
    {
        return new Builder();
    }
}
"#,
    )
    .unwrap();

    std::fs::write(
        auth_dir.join("User.php"),
        r#"<?php
namespace Illuminate\Foundation\Auth;

use Illuminate\Database\Eloquent\Model;

class User extends Model {}
"#,
    )
    .unwrap();

    std::fs::write(
        app_dir.join("User.php"),
        r#"<?php
namespace App\Models;

use Illuminate\Foundation\Auth\User as Authenticatable;

class User extends Authenticatable {}
"#,
    )
    .unwrap();

    let scratch_src = "<?php\n\\App\\Models\\User::where('id', 1)->";
    let scratch_file = tmp.path().join("scratch.php");
    std::fs::write(&scratch_file, scratch_src).unwrap();

    let mut s = TestServer::with_root(tmp.path()).await;
    s.validate_syntax(false);
    s.wait_for_index_ready().await;
    s.open("scratch.php", scratch_src).await;

    let uri = s.uri("scratch.php");
    let resp = s
        .client()
        .request(
            "textDocument/completion",
            serde_json::json!({
                "textDocument": { "uri": uri },
                "position": { "line": 1, "character": 34 },
                "context": { "triggerKind": 1 },
            }),
        )
        .await;

    let rendered = render_completion_ordered(&resp);
    expect![[r#"
        Method      first
        Method      get
        Method      orderBy
        Method      where"#]]
    .assert_eq(&members(&rendered));
}

