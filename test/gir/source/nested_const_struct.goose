struct Inner { value: i64 }
struct NestedConstStruct { values: (const Inner)[2] }

fn main() {
    let value = NestedConstStruct { values: [Inner { value: 1 }, Inner { value: 2 }] };
    print(value.values[0].value);
}
