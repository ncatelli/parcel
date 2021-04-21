# parcel
## Table of Contents
<!-- TOC -->

- [parcel](#parcel)
    - [Table of Contents](#table-of-contents)
    - [General](#general)
    - [Usage](#usage)
        - [Testing](#testing)
            - [Benchmark tests](#benchmark-tests)
    - [Warnings](#warnings)

<!-- /TOC -->

## General
A parser combinator library for rust.

## Usage
### Testing
Tests and documentation are provided primarily via docstring examples primarily but a few tests are additionally provided through standard rust unit testing and can be run via:

```
cargo test
```

#### Benchmark tests
Additionally benchmark tests are provided via `criterion` and can be run via:

```
cargo bench
```

## Warnings
Please nobody use this. This is entirely an experiment to support insane restrictions I've imposed on myself to build a computer from first principles.

Instead, please use the wonderful [geal/nom](https://github.com/Geal/nom) project that is better supported, better engineered and WAY more mature... frankly I don't even know why you are even looking at this.