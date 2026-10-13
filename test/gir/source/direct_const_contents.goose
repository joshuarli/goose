struct DirectConstContents { values: const i64[2] }

fn main() {
    let value = DirectConstContents { values: [1, 2] };
    print(value.values[0]);
}
