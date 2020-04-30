#[cfg(test)]
mod tests;

pub type ParseResult<'a, Input, Output> = Result<(&'a Input, Output), &'a Input>;

pub trait Parser<'a, Input, Output> {
    fn parse(&self, input: &'a Input) -> ParseResult<'a, Input, Output>;

    fn map<F, NewOutput>(self, map_fn: F) -> BoxedParser<'a, Input, NewOutput>
    where
        Self: Sized + 'a,
        Output: 'a,
        Input: Sized + 'a,
        NewOutput: 'a,
        F: Fn(Output) -> NewOutput + 'a,
    {
        BoxedParser::new(map(self, map_fn))
    }

    fn and_then<F, NextParser, NewOutput>(self, f: F) -> BoxedParser<'a, Input, NewOutput>
    where
        Self: Sized + 'a,
        Output: 'a,
        Input: Sized + 'a,
        NewOutput: 'a,
        NextParser: Parser<'a, Input, NewOutput> + 'a,
        F: Fn(Output) -> NextParser + 'a,
    {
        BoxedParser::new(and_then(self, f))
    }

    fn or<P>(self, thunk_to_parser: impl Fn() -> P + 'a) -> BoxedParser<'a, Input, Output>
    where
        Self: Sized + 'a,
        Input: 'a,
        Output: 'a,
        P: Parser<'a, Input, Output> + 'a,
    {
        BoxedParser::new(either(self, thunk_to_parser))
    }
}

impl<'a, F, Input, Output> Parser<'a, Input, Output> for F
where
    Input: 'a,
    F: Fn(&'a Input) -> ParseResult<Input, Output>,
{
    fn parse(&self, input: &'a Input) -> ParseResult<'a, Input, Output> {
        self(input)
    }
}

pub struct BoxedParser<'a, Input, Output> {
    parser: Box<dyn Parser<'a, Input, Output> + 'a>,
}

impl<'a, Input, Output> BoxedParser<'a, Input, Output> {
    fn new<P>(parser: P) -> Self
    where
        P: Parser<'a, Input, Output> + 'a,
    {
        BoxedParser {
            parser: Box::new(parser),
        }
    }
}

impl<'a, Input, Output> Parser<'a, Input, Output> for BoxedParser<'a, Input, Output> {
    fn parse(&self, input: &'a Input) -> ParseResult<'a, Input, Output> {
        self.parser.parse(input)
    }
}

fn either<'a, P1, P2, A: 'a, B>(
    parser1: P1,
    thunk_to_parser: impl Fn() -> P2,
) -> impl Parser<'a, A, B>
where
    P1: Parser<'a, A, B>,
    P2: Parser<'a, A, B>,
{
    move |input| match parser1.parse(input) {
        ok @ Ok(_) => ok,
        Err(_) => thunk_to_parser().parse(input),
    }
}

fn map<'a, P, F, A: 'a, B, C>(parser: P, map_fn: F) -> impl Parser<'a, A, C>
where
    P: Parser<'a, A, B>,
    F: Fn(B) -> C + 'a,
{
    move |input| {
        parser
            .parse(input)
            .map(|(next_input, result)| (next_input, map_fn(result)))
    }
}

fn and_then<'a, P, F, A: 'a, B, C, NextP>(parser: P, f: F) -> impl Parser<'a, A, C>
where
    P: Parser<'a, A, B>,
    NextP: Parser<'a, A, C>,
    F: Fn(B) -> NextP,
{
    move |input| match parser.parse(input) {
        Ok((next_input, result)) => f(result).parse(next_input),
        Err(err) => Err(err),
    }
}

#[allow(dead_code)]
fn take_while<'a, P, A: 'a, B>(parser: P) -> impl Parser<'a, A, Vec<B>>
where
    P: Parser<'a, A, B>,
{
    move |mut input| {
        let mut result_acc: Vec<B> = Vec::new();
        while let Ok((next_input, result)) = parser.parse(input) {
            input = next_input;
            result_acc.push(result);
        }

        Ok((input, result_acc))
    }
}

#[allow(dead_code)]
fn join<'a, P1, P2, A: 'a, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, A, (R1, R2)>
where
    P1: Parser<'a, A, R1>,
    P2: Parser<'a, A, R2>,
{
    move |input| {
        parser1.parse(input).and_then(|(next_input, result1)| {
            parser2
                .parse(next_input)
                .map(|(last_input, result2)| (last_input, (result1, result2)))
        })
    }
}

#[allow(dead_code)]
fn left<'a, P1: 'a, P2: 'a, A: 'a, R1: 'a, R2: 'a>(
    parser1: P1,
    parser2: P2,
) -> impl Parser<'a, A, R1>
where
    P1: Parser<'a, A, R1>,
    P2: Parser<'a, A, R2>,
{
    join(parser1, parser2).map(|(left, _right)| left)
}

#[allow(dead_code)]
fn right<'a, P1: 'a, P2: 'a, A: 'a, R1: 'a, R2: 'a>(
    parser1: P1,
    parser2: P2,
) -> impl Parser<'a, A, R2>
where
    P1: Parser<'a, A, R1>,
    P2: Parser<'a, A, R2>,
{
    join(parser1, parser2).map(|(_left, right)| right)
}

#[allow(dead_code)]
fn unzip<A, B>(pair: Vec<(A, B)>) -> (Vec<A>, Vec<B>) {
    let mut left_vec: Vec<A> = vec![];
    let mut right_vec: Vec<B> = vec![];
    pair.into_iter().for_each(|(left, right)| {
        left_vec.push(left);
        right_vec.push(right);
    });
    (left_vec, right_vec)
}
