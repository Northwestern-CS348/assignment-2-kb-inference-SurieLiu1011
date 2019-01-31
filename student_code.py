import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_remove(self, fact2):

        # remove unsupported facts and rules:
        if isinstance(fact2, Fact):
            if fact2 in self.facts:
                kb_fact = self._get_fact(fact2)
                if kb_fact.asserted and len(kb_fact.supported_by) == 0:
                    return
                if kb_fact.asserted == False and len(kb_fact.supported_by) == 0:
                    for fact in kb_fact.supports_facts:
                        removefact = []
                        fact = self._get_fact(fact)
                        length = len(fact.supported_by)
                        for i in range(0, length):
                            if fact.supported_by[i][0] == kb_fact:
                                removefact.append(i)
                        if len(removefact):
                            for k in removefact:
                                fact.supported_by.remove(fact.supported_by[k])
                        if len(fact.supported_by) == 0:
                            self.kb_remove(fact)

                    for rules in kb_fact.supports_rules:
                        removerule = []
                        lengthr = len(rules.supported_by)
                        rules = self._get_rule(rules)
                        for j in range(0, lengthr):
                            if rules.supported_by[j][0] == kb_fact:
                                removerule.append(j)
                        if len(removerule):
                            for k in removerule:
                                rules.supported_by.remove(rules.supported_by[k])
                        if len(rules.supported_by) == 0:
                            self.kb_remove(rules)

                    self.facts.remove(kb_fact)
            else:
                return

        if isinstance(fact2, Rule):
            if fact2 in self.rules:
                kb_rule = self._get_rule(fact2)
                if kb_rule.asserted:
                    return
                else:
                    if len(kb_rule.supported_by) == 0:
                        for facts in kb_rule.supports_facts:
                            facts = self._get_fact(facts)
                            removefact = []
                            length = len(facts.supported_by)

                            for i in range(0, length):
                                if facts.supported_by[i][1] == kb_rule:
                                    removefact.append(i)
                            if len(removefact):
                                for k in removefact:
                                    facts.supported_by.remove(facts.supported_by[k])
                            if len(facts.supported_by) == 0:
                                self.kb_remove(facts)

                        for rules in kb_rule.supports_rules:
                            rules = self._get_rule(rules)
                            removerule = []
                            lengthr = len(rules.supported_by)
                            for j in range(0, lengthr):
                                if rules.supported_by[j][1] == kb_rule:
                                    removerule.append(j)
                            if len(removerule):
                                for k in removerule:
                                    rules.supported_by.remove(rules.supported_by[k])
                            if len(rules.supported_by) == 0:
                                self.kb_remove(rules)
                        self.rules.remove(kb_rule)
            else:
                return


    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        if not isinstance(fact_or_rule, Fact) and not isinstance(fact_or_rule, Rule):
            print("Only facts and rules can be retracted.")
            return

        if isinstance(fact_or_rule, Fact):
            for item in self.facts:
                if item == fact_or_rule:
                    fact_or_rule = item
                    break
            else:
                print("Fact is not in KB.")
                return

        if isinstance(fact_or_rule, Rule):
            for item in self.rules:
                if item == fact_or_rule:
                    fact_or_rule = item
                    break
            else:
                print("Rule is not in KB.")
                return
        # first iteration:
        if isinstance(fact_or_rule, Fact):
            kb_fact = self._get_fact(fact_or_rule)
            # remove if unsupported:
            if len(kb_fact.supported_by) == 0:
                # adjust if support others:
                for facts in kb_fact.supports_facts:
                    facts = self._get_fact(facts)
                    removefact = []
                    length = len(facts.supported_by)
                    for i in range(0, length):
                        if facts.supported_by[i][0] == kb_fact:
                            removefact.append(i)
                    if len(removefact):
                        for k in removefact:
                            facts.supported_by.remove(facts.supported_by[k])

                    if len(facts.supported_by) == 0:
                        self.kb_remove(facts)

                for rules in kb_fact.supports_rules:
                    rules = self._get_rule(rules)
                    removerule = []
                    lengthr = len(rules.supported_by)

                    for j in range(0, lengthr):
                        if rules.supported_by[j][0] == kb_fact:
                            removerule.append(j)
                    if len(removerule):
                        for k in removerule:
                            rules.supported_by.remove(rules.supported_by[k])

                    if len(rules.supported_by) == 0:
                        self.kb_remove(rules)

                self.facts.remove(kb_fact)

            # adjust if supported
            if kb_fact.supported_by:
                for pair in kb_fact.supported_by:
                    f = self._get_fact(pair[0])
                    r = self._get_rule(pair[1])
                    f.supports_facts.remove(kb_fact)
                    r.supports_facts.remove(kb_fact)
                #kb_fact.asserted = False

        else:
            return


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        lhs_length = len(rule.lhs)
        binding = match(fact.statement, rule.lhs[0])
        #print(rule.lhs[0])

        if binding:
            #print("the length of lhs is:",len(rule.lhs))
            if lhs_length == 1:
                #add a new fact:
                #print("adding a new fact:")
                new_statement = instantiate(rule.rhs, binding)
                new_fact = Fact(new_statement, [[fact, rule]])
                #print("new fact is", new_fact)
                kb.kb_assert(new_fact)

                IndexOfNewFact = kb.facts.index(new_fact)
                # kb.facts[IndexOfNewFact].supported_by.append(supported_by)
                #kb.facts[IndexOfNewFact].asserted = False
                IndexOfFact = kb.facts.index(fact)
                kb.facts[IndexOfFact].supports_facts.append(new_fact)
                IndexOfRule = kb.rules.index(rule)
                kb.rules[IndexOfRule].supports_facts.append(new_fact)

            else:
                #add a new rule:
                #print("adding a new rule:")
                lhs_list = []
                for item in rule.lhs[1:]:
                    lhs = instantiate(item, binding)
                    lhs_list.append(lhs)
                    #print(lhs_list)
                rhs = instantiate(rule.rhs, binding)
                #print(rhs)
                new_rule = Rule([lhs_list, rhs], [[fact, rule]])
                #print("new rule is", new_rule)
                kb.kb_assert(new_rule)
                IndexOfNewRule = kb.rules.index(new_rule)

                # kb.rules[IndexOfNewRule].supported_by.append(supported_by)
                #kb.rules[IndexOfNewRule].asserted = False
                IndexOfRule = kb.rules.index(rule)
                kb.rules[IndexOfRule].supports_rules.append(new_rule)
                IndexOfFact = kb.facts.index(fact)
                kb.facts[IndexOfFact].supports_rules.append(new_rule)

