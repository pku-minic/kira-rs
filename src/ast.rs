pub struct CompUnit {
  pub items: Vec<GlobalItem>,
}

pub enum GlobalItem {
  Decl(Decl),
  FuncDef(FuncDef),
}

pub enum Decl {
  Const(ConstDecl),
  Var(VarDecl),
}

pub struct ConstDecl {
  pub defs: Vec<ConstDef>,
}

pub struct ConstDef {
  pub id: String,
  pub dims: Vec<ConstExp>,
  pub init: ConstInitVal,
}

pub enum ConstInitVal {
  Exp(ConstExp),
  List(Vec<ConstInitVal>),
}

pub struct VarDecl {
  pub defs: Vec<VarDef>,
}

pub struct VarDef {
  pub id: String,
  pub dims: Vec<ConstExp>,
  pub init: Option<InitVal>,
}

pub enum InitVal {
  Exp(Exp),
  List(Vec<InitVal>),
}

pub struct FuncDef {
  pub ty: FuncType,
  pub id: String,
  pub params: Vec<FuncFParam>,
  pub block: Block,
}

pub enum FuncType {
  Void,
  Int,
}

pub struct FuncFParam {
  pub id: String,
  pub dims: Option<Vec<ConstExp>>,
}

pub struct Block {
  pub items: Vec<BlockItem>,
}

pub enum BlockItem {
  Decl(Decl),
  Stmt(Stmt),
}

#[allow(clippy::enum_variant_names)]
pub enum Stmt {
  Assign(Assign),
  ExpStmt(ExpStmt),
  Block(Block),
  If(Box<If>),
  While(Box<While>),
  Break(Break),
  Continue(Continue),
  Return(Return),
}

pub struct Assign {
  pub lval: LVal,
  pub exp: Exp,
}

pub struct ExpStmt {
  pub exp: Option<Exp>,
}

pub struct If {
  pub cond: Exp,
  pub then: Stmt,
  pub else_then: Option<Stmt>,
}

pub struct While {
  pub cond: Exp,
  pub body: Stmt,
}

pub struct Break;

pub struct Continue;

pub struct Return {
  pub exp: Option<Exp>,
}

pub struct Exp {
  pub lor: LOrExp,
}

pub struct LVal {
  pub id: String,
  pub indices: Vec<Exp>,
}

pub enum PrimaryExp {
  Exp(Box<Exp>),
  LVal(LVal),
  Number(i32),
}

pub enum UnaryExp {
  Primary(PrimaryExp),
  Call(FuncCall),
  Unary(UnaryOp, Box<UnaryExp>),
}

pub struct FuncCall {
  pub id: String,
  pub args: Vec<Exp>,
}

pub enum MulExp {
  Unary(UnaryExp),
  MulUnary(Box<MulExp>, MulOp, UnaryExp),
}

pub enum AddExp {
  Mul(MulExp),
  AddMul(Box<AddExp>, AddOp, MulExp),
}

pub enum RelExp {
  Add(AddExp),
  RelAdd(Box<RelExp>, RelOp, AddExp),
}

pub enum EqExp {
  Rel(RelExp),
  EqRel(Box<EqExp>, EqOp, RelExp),
}

pub enum LAndExp {
  Eq(EqExp),
  LAndEq(Box<LAndExp>, EqExp),
}

pub enum LOrExp {
  LAnd(LAndExp),
  LOrLAnd(Box<LOrExp>, LAndExp),
}

pub struct ConstExp {
  pub exp: Exp,
}

pub enum UnaryOp {
  Neg,
  LNot,
}

pub enum MulOp {
  Mul,
  Div,
  Mod,
}

pub enum AddOp {
  Add,
  Sub,
}

pub enum RelOp {
  Lt,
  Gt,
  Le,
  Ge,
}

pub enum EqOp {
  Eq,
  Neq,
}
