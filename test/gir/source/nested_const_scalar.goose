struct NestedConstScalar { values: (const i64)[2] }

fn main() {
    let value = NestedConstScalar { values: [1, 2] };
    print(value.values[0]);
}
