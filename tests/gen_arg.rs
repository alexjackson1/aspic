use aspic::{
    generate_af,
    parse::{Formula, Predicate},
    SystemDescription,
};

#[test]
fn test_toast_example() {
    let description = SystemDescription::parse(
        "",
        r"
            snores(bob);
            professor(bob);
        ",
        r"
        snores(X) < professor(X);
    ",
        r"
            [r1]: snores(X) => misbehaves(X);
            [r2]: misbehaves(X) => accessDenied(X);
            [r3]: professor(X) => accessAllowed(X);
        ",
        r"
            [r1] < [r2];
            [r1] < [r3];
            [r3] < [r2];
        ",
        r"
            accessDenied(X)-accessAllowed(X);
        ",
    )
    .expect("Failed to parse input data");
    let framework = generate_af(description).expect("Failed to generate argumentation framework");

    // We expect the following arguments in any order
    // snores(bob)
    // professor(bob)
    // professor(bob) => accessAllowed(bob)
    // snores(bob) => misbehaves(bob)
    // misbehaves(bob) => accessDenied(bob)

    assert_eq!(framework.arguments.len(), 5);

    // Find the atomic arguments
    let atomic_args = framework
        .arguments
        .values()
        .filter(|arg| arg.top_rule.is_none())
        .collect::<Vec<_>>();

    assert_eq!(atomic_args.len(), 2);
    let snores_bob = Formula::Predicate(Predicate::new("snores".into(), vec!["bob".into()]));
    let professor_bob = Formula::Predicate(Predicate::new("professor".into(), vec!["bob".into()]));
    let mut snores_bob_id = None;
    let mut professor_bob_id = None;
    for arg in atomic_args {
        match &arg.conclusion {
            c if *c == snores_bob => {
                snores_bob_id = Some(arg.id);
            }
            c if *c == professor_bob => {
                professor_bob_id = Some(arg.id);
            }
            _ => {}
        }
    }

    assert!(snores_bob_id.is_some());
    assert!(professor_bob_id.is_some());

    // Find the non-atomic arguments
    let non_atomic_args = framework
        .arguments
        .values()
        .filter(|arg| arg.top_rule.is_some())
        .collect::<Vec<_>>();

    assert_eq!(non_atomic_args.len(), 3);

    let mut access_allowed_id = None;
    let mut misbehaves_bob_id = None;
    let mut access_denied_bob_id = None;

    let access_allowed_bob =
        Formula::Predicate(Predicate::new("accessAllowed".into(), vec!["bob".into()]));
    let access_denied_bob =
        Formula::Predicate(Predicate::new("accessDenied".into(), vec!["bob".into()]));
    let misbehaves_bob =
        Formula::Predicate(Predicate::new("misbehaves".into(), vec!["bob".into()]));

    for arg in non_atomic_args {
        match &arg.conclusion {
            c if *c == access_allowed_bob => {
                access_allowed_id = Some(arg.id);
            }
            c if *c == access_denied_bob => {
                access_denied_bob_id = Some(arg.id);
            }
            c if *c == misbehaves_bob => {
                misbehaves_bob_id = Some(arg.id);
            }
            _ => {}
        }
    }

    assert!(access_allowed_id.is_some());
    assert!(misbehaves_bob_id.is_some());
    assert!(access_denied_bob_id.is_some());

    println!("{}", framework);

    assert!(framework[access_allowed_id.unwrap()]
        .sub_args
        .contains(&professor_bob_id.unwrap()));
    assert!(framework[misbehaves_bob_id.unwrap()]
        .sub_args
        .contains(&snores_bob_id.unwrap()));
    assert!(framework[access_denied_bob_id.unwrap()]
        .sub_args
        .contains(&misbehaves_bob_id.unwrap()));
}
