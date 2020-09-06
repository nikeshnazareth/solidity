contract D {}

contract C {
    C c;
    D d;

    function foo() public {
        super != c;
        c != super;

        super != d;
        d != super;

        super != this;
        this != super;
    }
}
// ----
// TypeError 2271: (83-93): Operator != not compatible with types contract super C and contract C
// TypeError 2271: (103-113): Operator != not compatible with types contract C and contract super C
// TypeError 2271: (124-134): Operator != not compatible with types contract super C and contract D
// TypeError 2271: (144-154): Operator != not compatible with types contract D and contract super C
// TypeError 2271: (165-178): Operator != not compatible with types contract super C and contract C
// TypeError 2271: (188-201): Operator != not compatible with types contract C and contract super C
