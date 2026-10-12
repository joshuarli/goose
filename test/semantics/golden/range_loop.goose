fn main() {
    var fixed: i64[4] = [1, 2, 3, 4];
    var fixed_sum: i64 = 0;
    for i in 0..fixed.len {
        fixed_sum += fixed[i];
    }
    print("fixed ", fixed_sum);

    var grown: i64[>..] = [10, 20];
    var grown_sum: i64 = 0;
    for i in 0..grown.len {
        grown_sum += grown[i];
        if i < 2 {
            grown.push(i + 100);
        }
    }
    print("grown ", grown_sum, " ", grown.len);

    var n: i64 = 0;
    var total: i64 = 0;
    while true {
        n += 1;
        if n > 5 {
            break;
        }
        total += n;
    }
    print("while ", total, " ", n);
}
