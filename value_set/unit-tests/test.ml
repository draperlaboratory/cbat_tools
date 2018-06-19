open OUnit2;;

module ClpSet = Cbat_clp_set_composite;;
module TestComposite = Clp_test.Make(ClpSet)(ClpSet);;
module TestClp = Clp_test.Make(Cbat_clp)(struct let of_clp = fun x -> x end);;

run_test_tt_main begin "All tests">:::[
    Word_ops_test.all_tests;
    TestClp.all_tests;
    TestComposite.all_tests;
    Map_lattice_test.all_tests;
    Ai_memmap_test.all_tests;
] end;;

