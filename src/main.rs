use clap::Parser;
use rustyline::DefaultEditor;
use std::{collections::HashMap, fs::read_to_string, process::exit};

#[derive(Parser, Debug)]
#[command(name = "Pravda", version = "0.1.0")]
struct Cli {
    /// Script file to be running
    #[arg(index = 1)]
    file: Option<String>,
}

fn main() {
    let cli = Cli::parse();
    let mut scope: HashMap<String, Type> = builtin_function();

    if let Some(path) = cli.file {
        if let Ok(code) = read_to_string(path) {
            run_program(code, &mut scope);
        } else {
            eprintln!("Error! opening file is fault");
        }
    } else {
        println!("NormScript");
        let mut rl = DefaultEditor::new().unwrap();

        loop {
            if let Ok(code) = rl.readline("> ") {
                let code = code.trim().to_string();
                if code.is_empty() {
                    continue;
                }

                rl.add_history_entry(&code).unwrap_or_default();
                if let Some(ast) = run_program(code, &mut scope) {
                    println!("{}", ast.display(&mut scope));
                }
            }
        }
    }
}

fn builtin_function() -> HashMap<String, Type> {
    HashMap::from([
        (
            "max".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                args.get(0)?
                    .eval(scope)?
                    .get_array()
                    .iter()
                    .cloned()
                    .reduce(|a, c| {
                        let a = a.eval(scope).unwrap().get_number();
                        let c = c.eval(scope).unwrap().get_number();
                        if a > c {
                            Expr::Value(Type::Number(a))
                        } else {
                            Expr::Value(Type::Number(c))
                        }
                    })?
                    .eval(scope)
            })),
        ),
        (
            "min".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                args.get(0)?
                    .eval(scope)?
                    .get_array()
                    .iter()
                    .cloned()
                    .reduce(|a, c| {
                        let a = a.eval(scope).unwrap().get_number();
                        let c = c.eval(scope).unwrap().get_number();
                        if a < c {
                            Expr::Value(Type::Number(a))
                        } else {
                            Expr::Value(Type::Number(c))
                        }
                    })?
                    .eval(scope)
            })),
        ),
        (
            "len".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                Some(Type::Number(
                    args.get(0)?.eval(scope)?.get_array().len() as f64
                ))
            })),
        ),
        (
            "filter".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                let mut result = vec![];
                let func = args.get(1)?.eval(scope)?.get_function();
                for target in args.get(0)?.eval(scope)?.get_array() {
                    if Expr::Function(func.clone(), vec![target.clone()])
                        .eval(scope)?
                        .get_bool()
                    {
                        result.push(target);
                    }
                }
                Some(Type::Array(result))
            })),
        ),
        (
            "map".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                let mut result = vec![];
                let func = args.get(1)?.eval(scope)?.get_function();
                for target in args.get(0)?.eval(scope)?.get_array() {
                    result.push(Expr::Value(
                        Expr::Function(func.clone(), vec![target]).eval(scope)?,
                    ));
                }
                Some(Type::Array(result))
            })),
        ),
        (
            "reduce".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                let mut result = args.get(1)?.eval(scope)?;
                let func = args.get(2)?.eval(scope)?.get_function();
                for target in args.get(0)?.eval(scope)?.get_array() {
                    result = Expr::Function(func.clone(), vec![target, Expr::Value(result)])
                        .eval(scope)?;
                }
                Some(result)
            })),
        ),
        (
            "range".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                Some(Type::Array(
                    (args.get(0)?.eval(scope)?.get_number() as usize
                        ..args.get(1)?.eval(scope)?.get_number() as usize)
                        .step_by(args.get(2)?.eval(scope)?.get_number() as usize)
                        .map(|x| Expr::Value(Type::Number(x as f64)))
                        .collect(),
                ))
            })),
        ),
        (
            "split".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                Some(Type::Array(
                    args.get(0)?
                        .eval(scope)?
                        .get_string()
                        .split(&args.get(1)?.eval(scope)?.get_string())
                        .map(|x| Expr::Value(Type::String(x.to_string())))
                        .collect(),
                ))
            })),
        ),
        (
            "join".to_string(),
            Type::Function(Function::BuiltIn(|args, scope| {
                Some(Type::String(
                    args.get(0)?
                        .eval(scope)?
                        .get_array()
                        .iter()
                        .map(|x| x.eval(scope).unwrap().get_string())
                        .collect::<Vec<String>>()
                        .join(&args.get(1)?.eval(scope)?.get_string()),
                ))
            })),
        ),
        (
            "exit".to_string(),
            Type::Function(Function::BuiltIn(|_, _| exit(0))),
        ),
        ("new-line".to_string(), Type::String("\n".to_string())),
        ("double-quote".to_string(), Type::String("\"".to_string())),
    ])
}

fn run_program(source: String, scope: &mut HashMap<String, Type>) -> Option<Type> {
    let program = parse_program(source, scope).unwrap_or_default();
    run_block(program, scope)
}

fn run_block(block: Block, scope: &mut HashMap<String, Type>) -> Option<Type> {
    let mut result = Some(Type::Null);
    for mut line in block {
        result = line.run(scope);
    }
    result
}

fn parse_program(source: String, scope: &mut HashMap<String, Type>) -> Option<Block> {
    let mut program: Block = vec![];
    for code in tokenize_program(source) {
        let code = code.trim().to_string();
        if code.starts_with("if") {
            let tokens = tokenize_expr(code["if".len()..].trim().to_string())?;
            if tokens.get(2).unwrap_or(&"".to_string()).trim() == "else" {
                program.push(Statement::If(
                    parse_expr(tokens.get(0)?.to_owned(), scope)?,
                    parse_program(
                        {
                            let token = tokens.get(1)?.to_owned();
                            token[token.find("{")? + 1..token.rfind("}")?].to_string()
                        },
                        scope,
                    )?,
                    parse_program(
                        {
                            let token = tokens.get(3)?.to_owned();
                            token[token.find("{")? + 1..token.rfind("}")?].to_string()
                        },
                        scope,
                    ),
                ))
            } else {
                program.push(Statement::If(
                    parse_expr(tokens.get(0)?.to_owned(), scope)?,
                    parse_program(
                        {
                            let token = tokens.get(1)?.to_owned();
                            token[token.find("{")? + 1..token.rfind("}")?].to_string()
                        },
                        scope,
                    )?,
                    None,
                ))
            }
        } else if code.starts_with("print") {
            let expr = parse_expr(code["print".len()..code.len()].to_string(), scope)?;
            program.push(Statement::Print(expr))
        } else if code.starts_with("let") {
            let name = code["let".len()..code.find("=")?].trim().to_string();
            let expr = parse_program(code[code.find("=")? + 2..code.len()].to_string(), scope)?;
            program.push(Statement::Let(name, expr))
        } else if code.starts_with("while") {
            let tokens = tokenize_expr(code["while".len()..].trim().to_string())?;
            let expr = parse_expr(tokens.get(0)?.to_string(), scope)?;

            let code = tokens.get(1)?;
            let code_loop = parse_program(
                code[code.find("{")? + 1..code.rfind("}")?].to_string(),
                scope,
            )?;
            program.push(Statement::While(expr, code_loop))
        } else if code.starts_with("function") {
            let tokens = tokenize_expr(code["function".len()..].trim().to_string())?;
            let name = tokens.get(0)?.trim().to_string();

            let code = tokens.get(1)?;
            let args = tokenize_args(code[code.find("(")? + 1..code.rfind(")")?].to_string())?;

            let code = tokens.get(2)?;
            let code = parse_program(
                code[code.find("{")? + 1..code.rfind("}")?].to_string(),
                scope,
            )?;
            program.push(Statement::Function(name, args, code))
        } else if code.starts_with("for") {
            let tokens = tokenize_expr(code["for".len()..].trim().to_string())?;
            if tokens.get(1)? == "in" {
                let counter = tokens.get(0)?.trim().to_string();

                let code = tokens.get(2)?;
                let iter = parse_expr(code.to_string(), scope)?;

                let code = tokens.get(3)?;
                let code = parse_program(
                    code[code.find("{")? + 1..code.rfind("}")?].to_string(),
                    scope,
                )?;
                program.push(Statement::For(counter, iter, code))
            }
        } else if code.starts_with("//") || code.is_empty() {
            continue;
        } else {
            program.push(Statement::Expr(parse_expr(code, scope)?))
        }
    }
    Some(program)
}
fn parse_expr(soruce: String, scope: &mut HashMap<String, Type>) -> Option<Expr> {
    let tokens: Vec<String> = tokenize_expr(soruce)?;
    let left = tokens.last()?.trim().to_string();
    let left = if let Ok(n) = left.parse::<f64>() {
        Expr::Value(Type::Number(n))
    } else if left.starts_with("!") {
        let mut left = left.clone();
        left.remove(0);
        Expr::Prefix(Box::new(Prefix {
            operator: Operator::Not,
            values: parse_expr(left.to_string(), scope)?,
        }))
    } else if left.starts_with("-") {
        let mut left = left.clone();
        left.remove(0);
        Expr::Prefix(Box::new(Prefix {
            operator: Operator::Sub,
            values: parse_expr(left.to_string(), scope)?,
        }))
    } else if left.starts_with('"') && left.ends_with('"') {
        let left = {
            let mut left = left.clone();
            left.remove(0);
            left.remove(left.len() - 1);
            left
        };
        Expr::Value(Type::String(left.to_string()))
    } else if left.starts_with('(') && left.ends_with(')') {
        let left = {
            let mut left = left.clone();
            left.remove(0);
            left.remove(left.len() - 1);
            left
        };
        parse_expr(left, scope)?
    } else if left.starts_with("function(") && left.ends_with('}') {
        let left = {
            let mut left = left.clone();
            left = left.replacen("function(", "", 1);
            left.remove(left.len() - 1);
            left
        };
        let splited = left.split_once("){").unwrap();
        let args = tokenize_args(splited.0.to_string())?
            .iter()
            .map(|x| x.trim().to_string())
            .collect();
        Expr::Value(Type::Function(Function::UserDefined(
            args,
            parse_program(splited.1.to_string(), scope)?,
        )))
    } else if left.starts_with('[') && left.ends_with(']') {
        let left = {
            let mut left = left.clone();
            left.remove(0);
            left.remove(left.len() - 1);
            left
        };
        Expr::Value(Type::Array(
            tokenize_args(left)?
                .iter()
                .map(|x| parse_expr(x.trim().to_string(), scope).unwrap())
                .collect(),
        ))
    } else if left.contains('(') && left.ends_with(')') {
        let mut left = left.clone();
        left.remove(left.len() - 1);
        let (func, args) = left.split_once("(").unwrap();
        Expr::Function(
            if let Type::Function(f) = parse_expr(func.to_string(), scope)?.eval(scope)? {
                f
            } else {
                return None;
            },
            tokenize_args(args.to_string())?
                .iter()
                .map(|x| parse_expr(x.to_owned(), scope).unwrap())
                .collect::<Vec<Expr>>(),
        )
    } else if left.contains('[') && left.ends_with(']') {
        let mut left = left.clone();
        left.remove(left.len() - 1);
        let (target, index) = left.split_once("[").unwrap();
        Expr::Access(
            Box::new(parse_expr(target.to_string(), scope)?),
            Box::new(parse_expr(index.to_string(), scope)?),
        )
    } else {
        Expr::Value(Type::Symbol(left))
    };

    if let Some(operator) = {
        let mut tokens = tokens.clone();
        tokens.reverse();
        tokens
    }
    .get(1)
    {
        let operator = match operator.as_str() {
            "+" => Operator::Add,
            "-" => Operator::Sub,
            "*" => Operator::Mul,
            "/" => Operator::Div,
            "%" => Operator::Mod,
            "^" => Operator::Pow,
            "==" => Operator::Equal,
            "<" => Operator::LessThan,
            ">" => Operator::GreaterThan,
            "&" => Operator::And,
            "|" => Operator::Or,
            _ => return None,
        };
        Some(Expr::Infix(Box::new(Infix {
            operator,
            values: (
                parse_expr(tokens.get(..tokens.len() - 2)?.to_vec().join(" "), scope)?,
                left,
            ),
        })))
    } else {
        return Some(left);
    }
}

fn tokenize_program(input: String) -> Vec<String> {
    let mut tokens: Vec<String> = Vec::new();
    let mut current_token = String::new();
    let mut in_parentheses: usize = 0;
    let mut in_quote = false;

    for c in input.chars() {
        match c {
            '{' | '(' | '[' if !in_quote => {
                current_token.push(c);
                in_parentheses += 1;
            }
            '}' | ')' | ']' if !in_quote => {
                current_token.push(c);
                in_parentheses -= 1;
            }
            ';' if !in_quote => {
                if in_parentheses != 0 {
                    current_token.push(c);
                } else if !current_token.is_empty() {
                    tokens.push(current_token.clone());
                    current_token.clear();
                }
            }
            '"' => {
                in_quote = !in_quote;

                current_token.push(c);
            }
            _ => {
                current_token.push(c);
            }
        }
    }

    if in_parentheses == 0 && !current_token.is_empty() {
        tokens.push(current_token.clone());
        current_token.clear();
    }
    tokens
}

fn tokenize_expr(input: String) -> Option<Vec<String>> {
    let mut tokens: Vec<String> = Vec::new();
    let mut current_token = String::new();
    let mut in_parentheses: usize = 0;
    let mut in_quote = false;

    for c in input.chars() {
        match c {
            '(' | '{' | '[' if !in_quote => {
                current_token.push(c);
                in_parentheses += 1;
            }
            ')' | '}' | ']' if !in_quote => {
                current_token.push(c);
                if in_parentheses > 0 {
                    in_parentheses -= 1;
                } else {
                    eprintln!("Error! there's duplicate end of the parentheses");
                    return None;
                }
            }
            ' ' | '　' | '\t' if !in_quote => {
                if in_parentheses != 0 {
                    current_token.push(c);
                } else if !current_token.is_empty() {
                    tokens.push(current_token.clone());
                    current_token.clear();
                }
            }
            '"' => {
                in_quote = !in_quote;
                current_token.push(c);
            }
            _ => {
                current_token.push(c);
            }
        }
    }

    // Syntax error check
    if in_quote {
        eprintln!("Error! there's not end of the quote");
        return None;
    }
    if in_parentheses != 0 {
        eprintln!("Error! there's not end of the parentheses");
        return None;
    }

    if in_parentheses == 0 && !current_token.is_empty() {
        tokens.push(current_token.clone());
        current_token.clear();
    }

    Some(tokens)
}

fn tokenize_args(input: String) -> Option<Vec<String>> {
    let mut tokens: Vec<String> = Vec::new();
    let mut current_token = String::new();
    let mut in_parentheses: usize = 0;
    let mut in_quote = false;

    for c in input.chars() {
        match c {
            '(' | '[' | '{' if !in_quote => {
                current_token.push(c);
                in_parentheses += 1;
            }
            ')' | ']' | '}' if !in_quote => {
                current_token.push(c);
                if in_parentheses > 0 {
                    in_parentheses -= 1;
                } else {
                    eprintln!("Error! there's duplicate end of the parentheses");
                    return None;
                }
            }
            ',' if !in_quote => {
                if in_parentheses != 0 {
                    current_token.push(c);
                } else if !current_token.is_empty() {
                    tokens.push(current_token.clone());
                    current_token.clear();
                }
            }
            '"' => {
                in_quote = !in_quote;
                current_token.push(c);
            }
            _ => {
                current_token.push(c);
            }
        }
    }

    // Syntax error check
    if in_quote {
        eprintln!("Error! there's not end of the quote");
        return None;
    }
    if in_parentheses != 0 {
        eprintln!("Error! there's not end of the parentheses");
        return None;
    }

    if in_parentheses == 0 && !current_token.is_empty() {
        tokens.push(current_token.clone());
        current_token.clear();
    }
    Some(tokens)
}

type Block = Vec<Statement>;
#[derive(Debug, Clone)]
enum Statement {
    Print(Expr),
    Let(String, Block),
    Function(String, Vec<String>, Block),
    If(Expr, Block, Option<Block>),
    While(Expr, Block),
    For(String, Expr, Block),
    Expr(Expr),
}

impl Statement {
    fn run(&mut self, scope: &mut HashMap<String, Type>) -> Option<Type> {
        let mut result = Type::Null;
        match &self {
            Statement::Expr(expr) => result = expr.eval(scope)?,
            Statement::Print(expr) => {
                result = expr.eval(scope)?;
                println!("{}", result.get_string());
            }
            Statement::Let(name, expr) => {
                result = run_block(expr.clone(), scope)?;
                scope.insert(name.to_string(), result.clone());
            }
            Statement::Function(name, args, block) => {
                scope.insert(
                    name.to_string(),
                    Type::Function(Function::UserDefined(args.clone(), block.clone())),
                );
            }
            Statement::If(expr, code_true, code_false) => {
                if expr.eval(scope)?.get_bool() {
                    result = run_block(code_true.to_vec(), scope)?;
                } else {
                    if let Some(code_false) = code_false {
                        result = run_block(code_false.to_vec(), scope)?;
                    }
                }
            }
            Statement::While(expr, code) => {
                while expr.eval(scope)?.get_bool() {
                    result = run_block(code.to_vec(), scope)?;
                }
            }
            Statement::For(counter, iterator, code) => {
                for i in iterator.eval(scope)?.get_array() {
                    result = i.eval(scope)?;
                    scope.insert(counter.clone(), result.clone());
                    result = run_block(code.to_vec(), scope)?;
                }
            }
        }
        Some(result)
    }
}

#[derive(Debug, Clone)]
enum Type {
    Number(f64),
    Bool(bool),
    String(String),
    Array(Vec<Expr>),
    Function(Function),
    Symbol(String),
    Null,
}

impl Type {
    fn get_number(&self) -> f64 {
        match self {
            Type::Number(n) => n.to_owned(),
            Type::String(s) | Type::Symbol(s) => s.trim().parse().unwrap_or(0.0),
            Type::Bool(b) => {
                if *b {
                    1.0
                } else {
                    0.0
                }
            }
            _ => 0.0,
        }
    }

    fn get_bool(&self) -> bool {
        match self {
            Type::Number(n) => *n != 0.0,
            Type::String(s) | Type::Symbol(s) => s.trim().parse().unwrap_or(false),
            Type::Bool(b) => *b,
            _ => false,
        }
    }

    fn get_string(&self) -> String {
        match self {
            Type::String(s) | Type::Symbol(s) => s.to_string(),
            Type::Number(n) => n.to_string(),
            Type::Bool(b) => b.to_string(),
            _ => String::new(),
        }
    }
    fn get_array(&self) -> Vec<Expr> {
        match self {
            Type::Array(s) => s.to_owned(),
            Type::String(s) => s
                .chars()
                .map(|x| Expr::Value(Type::String(x.to_string())))
                .collect(),
            other => vec![Expr::Value(other.to_owned())],
        }
    }
    fn get_function(&self) -> Function {
        match self {
            Type::Function(func) => func.clone(),
            _ => Function::UserDefined(vec![], vec![]),
        }
    }
    fn display(&self, scope: &mut HashMap<String, Type>) -> String {
        match self {
            Type::String(s) => format!("\"{}\"", s),
            Type::Symbol(s) => s.to_string(),
            Type::Number(n) => n.to_string(),
            Type::Bool(b) => b.to_string(),
            Type::Array(a) => format!(
                "[{}]",
                a.iter()
                    .map(|x| x.eval(scope).unwrap().display(scope))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Type::Null => "null".to_string(),
            Type::Function(Function::BuiltIn(f)) => format!("function({f:?})"),
            Type::Function(Function::UserDefined(args, _)) => {
                format!("function({})", args.join(", "))
            }
        }
    }
}

#[derive(Debug, Clone)]
enum Expr {
    Infix(Box<Infix>),
    Prefix(Box<Prefix>),
    Function(Function, Vec<Expr>),
    Access(Box<Expr>, Box<Expr>),
    Value(Type),
}

#[derive(Clone, Debug)]
enum Function {
    BuiltIn(fn(Vec<Expr>, &mut HashMap<String, Type>) -> Option<Type>),
    UserDefined(Vec<String>, Block),
}

impl Expr {
    fn eval(&self, scope: &mut HashMap<String, Type>) -> Option<Type> {
        Some(match self {
            Expr::Prefix(prefix) => (*prefix).eval(scope)?,
            Expr::Infix(infix) => (*infix).eval(scope)?,
            Expr::Value(value) => {
                if let Type::Symbol(name) = value {
                    if let Some(refer) = scope.get(name.as_str()).cloned() {
                        refer
                    } else {
                        value.clone()
                    }
                } else {
                    value.clone()
                }
            }
            Expr::Function(Function::BuiltIn(func), args) => func(args.to_owned(), scope)?,
            Expr::Function(Function::UserDefined(params, code), args) => {
                let mut scope = scope.clone();
                for i in params.iter().zip(args) {
                    let value = i.1.eval(&mut scope)?;
                    scope.insert(i.0.to_string(), value);
                }
                run_block(code.clone(), &mut scope)?
            }
            Expr::Access(target, index) => target
                .eval(scope)?
                .get_array()
                .iter()
                .map(|x| x.eval(scope).unwrap())
                .collect::<Vec<Type>>()
                .get(index.eval(scope)?.get_number() as usize)?
                .clone(),
        })
    }
}

#[derive(Debug, Clone)]
struct Infix {
    operator: Operator,
    values: (Expr, Expr),
}

#[derive(Debug, Clone)]
struct Prefix {
    operator: Operator,
    values: Expr,
}

#[derive(Debug, Clone)]
enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Equal,
    LessThan,
    GreaterThan,
    And,
    Or,
    Not,
}

impl Infix {
    fn eval(&self, scope: &mut HashMap<String, Type>) -> Option<Type> {
        let left = self.values.0.eval(scope)?;
        let right = self.values.1.eval(scope)?;
        Some(match self.operator {
            Operator::Add => {
                if let Type::Number(left) = left {
                    Type::Number(left + right.get_number())
                } else if let Type::String(left) = left {
                    Type::String(left + &right.get_string())
                } else if let Type::Array(left) = left {
                    Type::Array([left, right.get_array()].concat())
                } else {
                    Type::Null
                }
            }
            Operator::Sub => {
                if let Type::Number(left) = left {
                    Type::Number(left - right.get_number())
                } else if let Type::String(left) = left {
                    Type::String(left.replace(&right.get_string(), ""))
                } else {
                    Type::Null
                }
            }
            Operator::Mul => {
                if let Type::Number(left) = left {
                    Type::Number(left * right.get_number())
                } else if let Type::String(left) = left {
                    Type::String(left.repeat(right.get_number() as usize))
                } else {
                    Type::Null
                }
            }
            Operator::Div => Type::Number(left.get_number() / right.get_number()),
            Operator::Mod => Type::Number(left.get_number() % right.get_number()),
            Operator::Pow => Type::Number(left.get_number().powf(right.get_number())),
            Operator::Equal => Type::Bool(left.get_string() == right.get_string()),
            Operator::LessThan => Type::Bool(left.get_number() < right.get_number()),
            Operator::GreaterThan => Type::Bool(left.get_number() > right.get_number()),
            Operator::And => Type::Bool(left.get_bool() && right.get_bool()),
            Operator::Or => Type::Bool(left.get_bool() || right.get_bool()),
            _ => todo!(),
        })
    }
}

impl Prefix {
    fn eval(&self, scope: &mut HashMap<String, Type>) -> Option<Type> {
        let value = self.values.eval(scope)?;
        Some(match self.operator {
            Operator::Sub => Type::Number(-value.get_number()),
            Operator::Not => Type::Bool(!value.get_bool()),
            _ => todo!(),
        })
    }
}
