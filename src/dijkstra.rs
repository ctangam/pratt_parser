struct Lexer {
    tokens: Vec<char>,
}

impl Lexer {
    fn new(input: &str) -> Self {
        let mut tokens = input
            .chars()
            .filter(|c| !c.is_ascii_whitespace())
            .collect::<Vec<_>>();
        tokens.reverse();
        Self { tokens }
    }

    fn next(&mut self) -> Option<char> {
        self.tokens.pop()
    }

    fn peek(&mut self) -> Option<char> {
        self.tokens.last().copied()
    }
}

use std::fmt;

enum S {
    Cons(char, Vec<S>),
}

impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            S::Cons(head, rest) => {
                if rest.is_empty() {
                    write!(f, "{}", head)
                } else {
                    write!(f, "({}", head)?;
                    for s in rest {
                        write!(f, " {}", s)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

fn expr(input: &str) -> S {
    let mut lexer = Lexer::new(input);
    expr_bp(&mut lexer).unwrap()
}

struct Frame {
    min_bp: u8,
    lhs: Option<S>,
    token: Option<char>,
}

fn expr_bp(lexer: &mut Lexer) -> Option<S> {
    let mut top = Frame {
        min_bp: 0,
        lhs: None,
        token: None,
    };
    let mut stack = Vec::new();

    loop {
        let token = lexer.peek();

        let (token, r_bp) = match binding_power(token, top.lhs.is_none()) {
            Some((l_bp, r_bp)) if top.min_bp <= l_bp => (token?, r_bp),
            _ => {
                let res = top;
                top = match stack.pop() {
                    Some(it) => it,
                    None => return res.lhs,
                };
                if res.token == Some('(') {
                    assert_eq!(lexer.next(), Some(')'));
                    top.lhs = res.lhs;
                    continue;
                }
                let mut args = Vec::new();
                args.extend(top.lhs);
                args.extend(res.lhs);
                top.lhs = Some(S::Cons(res.token.unwrap(), args));
                continue;
            }
        };

        lexer.next();

        stack.push(top);
        top = Frame {
            min_bp: r_bp,
            lhs: None,
            token: Some(token),
        };
    }
}

fn binding_power(token: Option<char>, prefix: bool) -> Option<(u8, u8)> {
    let token = token?;
    let res = match token {
        '0'..='9' | 'a'..='z' | 'A'..='Z' => (99, 100),
        '(' => (99, 0),
        '=' => (2, 1),
        '+' | '-' if prefix => (99, 9),
        '+' | '-' => (5, 6),
        '*' | '/' => (7, 8),
        '!' => (11, 100),
        '.' => (14, 13),
        _ => return None,
    };

    Some(res)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_single_number() {
        let s = expr("1");
        assert_eq!(s.to_string(), "1");
    }

    #[test]
    fn test_expr_addition_and_multiplication() {
        let s = expr("1 + 2 * 3");
        assert_eq!(s.to_string(), "(+ 1 (* 2 3))");
    }

    #[test]
    fn test_expr_multiple_additions_and_multiplications() {
        let s = expr("a + b * c * d + e");
        assert_eq!(s.to_string(), "(+ (+ a (* (* b c) d)) e)");
    }

    #[test]
    fn test_expr_function_calls() {
        let s = expr("f . g . h");
        assert_eq!(s.to_string(), "(. f (. g h))");
    }

    #[test]
    fn test_expr_mixed_operations() {
        let s = expr(" 1 + 2 + f . g . h * 3 * 4");
        assert_eq!(s.to_string(), "(+ (+ 1 2) (* (* (. f (. g h)) 3) 4))");
    }

    #[test]
    fn test_expr_double_negation() {
        let s = expr("--1 * 2");
        assert_eq!(s.to_string(), "(* (- (- 1)) 2)");
    }

    #[test]
    fn test_expr_double_negation_function_call() {
        let s = expr("--f . g");
        assert_eq!(s.to_string(), "(- (- (. f g)))");
    }

    #[test]
    fn test_expr_negation_factorial() {
        let s = expr("-9!");
        assert_eq!(s.to_string(), "(- (! 9))");
    }

    #[test]
    fn test_expr_factorial() {
        let s = expr("3! * 4!");
        assert_eq!(s.to_string(), "(* (! 3) (! 4))");
    }

    #[test]
    fn test_expr_function_call_factorial() {
        let s = expr("f . g !");
        assert_eq!(s.to_string(), "(! (. f g))");
    }

    #[test]
    fn test_expr_nested_parentheses() {
        let s = expr("(((0)))");
        assert_eq!(s.to_string(), "0");
    }
}
