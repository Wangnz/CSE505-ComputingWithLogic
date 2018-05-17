
# coding: utf-8

# ## Implementation of FOLD algorithm

# ### Charuta Pethe
# ### CSE 505 Fall 2017
# ### Stony Brook University

# #### Initial imports, definitions and declarations

# In[1]:


from ast import literal_eval
import numpy as np
global ab_count
global goal
global abnormalRules


# In[2]:


class Rule():
    def __init__(self, head_arg, body_arg):
        self.head = head_arg
        self.body = body_arg

class Fact():
    def __init__(self, predicate_arg, parameter_arg):
        self.predicate = predicate_arg
        self.parameter = parameter_arg

class BackgroundKnowledge():
    def __init__(self, rules_arg, facts_arg):
        self.rules = rules_arg
        self.facts = facts_arg


# #### Function which generates and returns the next abnormal predicate

# In[3]:


def generate_next_ab_predicate():
    global ab_count
    temp = ab_count
    ab_count = ab_count + 1
    return "ab" + str(temp)


# #### Function to generate a predicate with a list of all examples as a string

# In[4]:


def enumerate_function(c, examples):
    newRule = Rule(head_arg = c.head, body_arg = [str(examples)])
    return newRule


# #### Function to check whether a constant is a member of an enumerated clause

# In[5]:


def checkmember(example, clause):
    list_clause = literal_eval(clause)
    if example in list_clause:
        return True
    return False


# #### Function to retuen a subset of the examples covered by the rule, given the background knowledge

# In[6]:


def coversHelper(rule, example, bk):

    for clause in rule.body:

        # for member check
        if clause[0] == '-' and clause[1] == '[':
            # if checkmember(example, clause[1:]) is True, return False, else continue
            if checkmember(example, clause[1:]) == True:
                return False
            continue
        if clause[0] == '[':
            # if checkmember(example, clause) is False, return False, else continue
            if checkmember(example, clause) == False:
                return False
            continue

        # for normal clauses
        if clause[0] != '-':
            for fact in bk.facts:
                flag = False
                if fact.predicate == clause and fact.parameter == example:
                    flag = True
                    break
            if(flag == True): # Clause is satisfied by making use of facts in database
                continue
            for r in bk.rules:
                flag = False
                if r.head == clause and coversHelper(r, example, bk): # clause is satisfied by making use of a rule
                    flag = True
                    break
            if flag == True:
                continue
            # If execution reaches here, clause could not be satisfied
            return False

        # for negated clauses
        else:
            #clause[0] == '-': - the rule is a negation
            clause = clause[1:]
            for fact in bk.facts:
                if fact.predicate == clause and fact.parameter == example:
                    return False
            for r in bk.rules:
                if r.head == clause and coversHelper(r, example, bk):
                    return False
            # If execution reaches here, clause could not be satisfied
            return True
    # If execution reaches here, the for loop ended, i.e. all clauses could be satisfied
    return True


def covers(c_hat, examples, bk):
    newExamples = list()
    for ex in examples:
        # if c_hat covers ex given bk, add it to newExamples
        if coversHelper(c_hat, ex, bk):
            newExamples.append(ex)
    return newExamples


# #### Function to select best literal from predicates, add it to the rule and return the new rule

# In[7]:


def addBestLiteral(c, positiveExamples, negativeExamples, predicates, bk):

    rules = dict()
    IGs = dict()

    for pred in predicates:

        p0 = len(covers(c, positiveExamples, bk))
        n0 = len(covers(c, negativeExamples, bk))

        tempBody = list(c.body)
        tempBody.append(pred)
        tempRule = Rule(head_arg = c.head, body_arg = tempBody)
        tempPositive = covers(tempRule, positiveExamples, bk)
        tempNegative = covers(tempRule, negativeExamples, bk)

        p1 = len(tempPositive)
        n1 = len(tempNegative)

        t = 0
        for elem in positiveExamples:
            if elem in tempPositive:
                t = t + 1

        if p1 == 0 or p0 == 0:
            continue

        IG = float(t) * (np.log2(float(p1) / (float(p1) + float(n1))) - np.log2(float(p0) / (float(p0) + float(n0))))

        if IG < 0:
            continue

        rules[pred] = tempRule
        IGs[pred] = IG

    if len(IGs.keys()) == 0:
        return 0, 0

    # select predicate with best IG and return
    best_pred = max(IGs.items(), key=lambda x: x[1])

    return rules[best_pred[0]], IGs[best_pred[0]]


# #### Exception function defined in the algorithm

# In[8]:


def exception(c, positiveExamples, negativeExamples, predicates_arg, bk):
    global abnormalRules
    predicates = list(predicates_arg)
    c_def, IG = addBestLiteral(c, positiveExamples, negativeExamples, predicates, bk)
    if(c_def != 0):
        # c_set is the set of default clauses returned by FOLD
        c_set = FOLD(positiveExamples, negativeExamples, predicates, bk)[0]
        # c_ab is a string - the next abnormal predicate
        c_ab = generate_next_ab_predicate()
        for c_var in c_set:
            tempRule = Rule(head_arg = c_ab, body_arg = c_var.body)
            abnormalRules.append(tempRule)
        tempBody = list(c.body)
        tempBody.append("-" + c_ab)
        c_hat = Rule(head_arg = c_def.head, body_arg = tempBody)
    else:
        c_hat = 0
    return c_hat


# #### Specialize function defined in the algorithm

# In[9]:


def specialize(c, positiveExamples, negativeExamples, predicates_arg, bk):
    predicates = list(predicates_arg)
    c_hat = c
    just_started = True
    while True:
        c_def, IG = addBestLiteral(c_hat, positiveExamples, negativeExamples, predicates, bk)
        if c_def != 0:
            c_hat = c_def
            predicates.remove(c_hat.body[0])
        elif just_started:
            c_hat = enumerate_function(c, positiveExamples)
        else:
            c_hat = exception(c_hat, negativeExamples, positiveExamples, predicates, bk)
            if c_hat == 0:
                c_hat = enumerate_function(c, positiveExamples)
        just_started = False
        for elem in abnormalRules:
            flag = False
            for r in bk.rules:
                if elem.head == r.head and elem.body == r.body:
                    flag = True
                    break
            if flag == False:
                bk.rules.append(elem)
        temp = covers(c_hat, positiveExamples, bk)
        # select the examples that are there in positiveExamples but not in temp
        newPositiveExamples = list()
        for elem in positiveExamples:
            if elem not in temp:
                newPositiveExamples.append(elem)
        # update positiveExamples
        positiveExamples = list(newPositiveExamples)
        # update negativeExamples
        negativeExamples = covers(c_hat, negativeExamples, bk)
        if len(negativeExamples) == 0:
            break
    return c_hat


# #### Function to implement FOLD algorithm

# In[10]:


def FOLD(positiveExamples, negativeExamples, predicates_arg, bk):
    global goal
    global abnormalRules
    predicates = list(predicates_arg)
    defaultRules = []
    while(len(positiveExamples) > 0):
        c = Rule(head_arg = goal, body_arg = [])
        c_hat = specialize(c, positiveExamples, negativeExamples, predicates, bk)
        temp = covers(c_hat, positiveExamples, bk)
        newPositiveExamples = list()
        for elem in positiveExamples:
            if elem not in temp:
                newPositiveExamples.append(elem)
        positiveExamples = list(newPositiveExamples)
        defaultRules.append(c_hat)
        for r in defaultRules:
            for elem in r.body:
                if elem in predicates:
                    predicates.remove(elem)
            flag = False
            for elem in bk.rules:
                if r.head == elem.head and r.body == elem.body:
                    flag = True
                    break
            if flag == False:
                bk.rules.append(r)
        for r in abnormalRules:
            flag = False
            for elem in bk.rules:
                if r.head == elem.head and r.body == elem.body:
                    flag = True
                    break
            if flag == False:
                bk.rules.append(r)
    return defaultRules, abnormalRules


# #### Function to print the result

# In[11]:


def prettyprint(result):
    for elem in result:
        for elem2 in elem:
            print elem2.head + "(X)" + " <-",
            for i in range(len(elem2.body)):
                elem3 = elem2.body[i]

                if elem3[0] == '-':
                    print "not",
                    elem3 = elem3[1:]

                if elem3[0] == '[':
                    print "member(X,", elem3, "\b)"
                    continue

                print elem3 + "(X)",
                if i == len(elem2.body) - 1:
                    print ""
                else:
                    print ",",


# # Testing

# ## Example 1 - All birds except penguins can fly

# In[12]:

print "\nExample 1:\n"

rule1 = Rule(head_arg = "bird", body_arg = ["penguin"])
rules = [rule1]

fact1 = Fact(predicate_arg = "bird", parameter_arg = "tweety")
fact2 = Fact(predicate_arg = "bird", parameter_arg = "et")
fact3 = Fact(predicate_arg = "cat", parameter_arg = "kitty")
fact4 = Fact(predicate_arg = "penguin", parameter_arg = "polly")

facts = [fact1, fact2, fact3, fact4]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)
goal = "fly"
positiveExamples = ["tweety", "et"]
negativeExamples = ["kitty", "polly"]

predicateList = ["bird", "cat", "penguin"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# ### The intuitive set of rules is that all birds except penguins can fly. The output of the algorithm matches this intuitive set of rules.

# ## Example 2 - Enumeration

# In[13]:

print "\nExample 2:\n"

rule1 = Rule(head_arg = "bird", body_arg = ["penguin"])
rules = [rule1]

fact1 = Fact(predicate_arg = "bird", parameter_arg = "tweety")
fact2 = Fact(predicate_arg = "bird", parameter_arg = "et")
fact3 = Fact(predicate_arg = "cat", parameter_arg = "kitty")
fact4 = Fact(predicate_arg = "penguin", parameter_arg = "polly")

facts = [fact1, fact2, fact3, fact4]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)
goal = "fly"
positiveExamples = ["tweety", "et", "jet"]
negativeExamples = ["kitty", "polly"]

predicateList = ["bird", "cat", "penguin"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# ### The intuitive set of rules is that all birds except penguins can fly, and that a jet can fly. The output of the algorithm matches this intuitive set of rules.

# ## Example 3 - Two rules and nested exception

# In[14]:

print "\nExample 3:\n"

rule1 = Rule(head_arg = "bird", body_arg = ["penguin"])
rule2 = Rule(head_arg = "penguin", body_arg = ["superpenguin"])
rules = [rule1, rule2]

fact1 = Fact(predicate_arg = "bird", parameter_arg = "a")
fact2 = Fact(predicate_arg = "bird", parameter_arg = "b")
fact3 = Fact(predicate_arg = "penguin", parameter_arg = "c")
fact4 = Fact(predicate_arg = "penguin", parameter_arg = "d")
fact5 = Fact(predicate_arg = "superpenguin", parameter_arg = "e")
fact6 = Fact(predicate_arg = "superpenguin", parameter_arg = "f")
fact7 = Fact(predicate_arg = "cat", parameter_arg = "c1")
fact8 = Fact(predicate_arg = "plane", parameter_arg = "g")
fact9 = Fact(predicate_arg = "plane", parameter_arg = "h")
fact10 = Fact(predicate_arg = "plane", parameter_arg = "k")
fact11 = Fact(predicate_arg = "plane", parameter_arg = "m")
fact12 = Fact(predicate_arg = "damaged", parameter_arg = "k")
fact13 = Fact(predicate_arg = "damaged", parameter_arg = "m")

facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)
goal = "fly"
positiveExamples = ["a", "b", "e", "f", "g", "h"]
negativeExamples = ["c", "d", "c1", "k", "m"]

predicateList = ["bird", "penguin", "superpenguin", "cat", "plane", "damaged"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# ### The intuitive set of rules is that all birds except penguins can fly with the exception that superpenguins can fly, and that all planes except damaged planes can fly. The output of the algorithm matches this intuitive set of rules.

# ## Example 4 - Blood donation compatibility

# ### Setting up the knowledge base

# In[29]:
print "\nExample 4:\n"

rules = []

fact1 = Fact(predicate_arg = "O", parameter_arg = "p1")
fact2 = Fact(predicate_arg = "O", parameter_arg = "p2")
fact3 = Fact(predicate_arg = "O", parameter_arg = "p3")
fact4 = Fact(predicate_arg = "O", parameter_arg = "p4")

fact1_1 = Fact(predicate_arg = "rh+", parameter_arg = "p1")
fact2_1 = Fact(predicate_arg = "rh+", parameter_arg = "p2")
fact3_1 = Fact(predicate_arg = "rh+", parameter_arg = "p3")
fact4_1 = Fact(predicate_arg = "rh+", parameter_arg = "p4")

fact5 = Fact(predicate_arg = "O", parameter_arg = "p5")
fact6 = Fact(predicate_arg = "O", parameter_arg = "p6")
fact7 = Fact(predicate_arg = "O", parameter_arg = "p7")
fact8 = Fact(predicate_arg = "O", parameter_arg = "p8")

fact5_1 = Fact(predicate_arg = "rh-", parameter_arg = "p5")
fact6_1 = Fact(predicate_arg = "rh-", parameter_arg = "p6")
fact7_1 = Fact(predicate_arg = "rh-", parameter_arg = "p7")
fact8_1 = Fact(predicate_arg = "rh-", parameter_arg = "p8")

fact9 = Fact(predicate_arg = "A", parameter_arg = "p9")
fact10 = Fact(predicate_arg = "A", parameter_arg = "p10")
fact11 = Fact(predicate_arg = "A", parameter_arg = "p11")
fact12 = Fact(predicate_arg = "A", parameter_arg = "p12")

fact9_1 = Fact(predicate_arg = "rh+", parameter_arg = "p9")
fact10_1 = Fact(predicate_arg = "rh+", parameter_arg = "p10")
fact11_1 = Fact(predicate_arg = "rh+", parameter_arg = "p11")
fact12_1 = Fact(predicate_arg = "rh+", parameter_arg = "p12")

fact13 = Fact(predicate_arg = "A", parameter_arg = "p13")
fact14 = Fact(predicate_arg = "A", parameter_arg = "p14")
fact15 = Fact(predicate_arg = "A", parameter_arg = "p15")
fact16 = Fact(predicate_arg = "A", parameter_arg = "p16")

fact13_1 = Fact(predicate_arg = "rh-", parameter_arg = "p13")
fact14_1 = Fact(predicate_arg = "rh-", parameter_arg = "p14")
fact15_1 = Fact(predicate_arg = "rh-", parameter_arg = "p15")
fact16_1 = Fact(predicate_arg = "rh-", parameter_arg = "p16")

fact17 = Fact(predicate_arg = "B", parameter_arg = "p17")
fact18 = Fact(predicate_arg = "B", parameter_arg = "p18")
fact19 = Fact(predicate_arg = "B", parameter_arg = "p19")
fact20 = Fact(predicate_arg = "B", parameter_arg = "p20")

fact17_1 = Fact(predicate_arg = "rh+", parameter_arg = "p17")
fact18_1 = Fact(predicate_arg = "rh+", parameter_arg = "p18")
fact19_1 = Fact(predicate_arg = "rh+", parameter_arg = "p19")
fact20_1 = Fact(predicate_arg = "rh+", parameter_arg = "p20")

fact21 = Fact(predicate_arg = "B", parameter_arg = "p21")
fact22 = Fact(predicate_arg = "B", parameter_arg = "p22")
fact23 = Fact(predicate_arg = "B", parameter_arg = "p23")
fact24 = Fact(predicate_arg = "B", parameter_arg = "p24")

fact21_1 = Fact(predicate_arg = "rh-", parameter_arg = "p21")
fact22_1 = Fact(predicate_arg = "rh-", parameter_arg = "p22")
fact23_1 = Fact(predicate_arg = "rh-", parameter_arg = "p23")
fact24_1 = Fact(predicate_arg = "rh-", parameter_arg = "p24")

fact25 = Fact(predicate_arg = "AB", parameter_arg = "p25")
fact26 = Fact(predicate_arg = "AB", parameter_arg = "p26")
fact27 = Fact(predicate_arg = "AB", parameter_arg = "p27")
fact28 = Fact(predicate_arg = "AB", parameter_arg = "p28")

fact25_1 = Fact(predicate_arg = "rh+", parameter_arg = "p25")
fact26_1 = Fact(predicate_arg = "rh+", parameter_arg = "p26")
fact27_1 = Fact(predicate_arg = "rh+", parameter_arg = "p27")
fact28_1 = Fact(predicate_arg = "rh+", parameter_arg = "p28")

fact29 = Fact(predicate_arg = "AB", parameter_arg = "p29")
fact30 = Fact(predicate_arg = "AB", parameter_arg = "p30")
fact31 = Fact(predicate_arg = "AB", parameter_arg = "p31")
fact32 = Fact(predicate_arg = "AB", parameter_arg = "p32")

fact29_1 = Fact(predicate_arg = "rh-", parameter_arg = "p29")
fact30_1 = Fact(predicate_arg = "rh-", parameter_arg = "p30")
fact31_1 = Fact(predicate_arg = "rh-", parameter_arg = "p31")
fact32_1 = Fact(predicate_arg = "rh-", parameter_arg = "p32")

facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

predicateList = ["O", "A", "B", "AB", "rh+", "rh-"]


# ### Who can donate to O+?

# In[16]:

print ""

goal = "donatestoO+"
positiveExamples = ["p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"]
negativeExamples = ["p9", "p10", "p11", "p12", "p13", "p14", "p15", "p16", "p17", "p18", "p19", "p20", "p21", "p22", "p23", "p24", "p25", "p26", "p27", "p28", "p29", "p30", "p31", "p32"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that only people with blood group O can donate to people with blood group O+. The output of the algorithm matches this expected set of rules.

# ### Who can donate to O-?

# In[18]:
print ""
rules = []
facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

goal = "donatestoO-"
positiveExamples = ["p5", "p6", "p7", "p8"]
negativeExamples = ["p1", "p2", "p3", "p4", "p9", "p10", "p11", "p12", "p13", "p14", "p15", "p16", "p17", "p18", "p19", "p20", "p21", "p22", "p23", "p24", "p25", "p26", "p27", "p28", "p29", "p30", "p31", "p32"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that only people with blood group O- can donate to people with blood group O-. The output of the algorithm matches this expected set of rules.

# ### Who can donate to B+?

# In[20]:
print ""
rules = []
facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

goal = "donatestoB+"
positiveExamples = ["p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8", "p17", "p18", "p19", "p20", "p21", "p22", "p23", "p24"]
negativeExamples = ["p9", "p10", "p11", "p12", "p13", "p14", "p15", "p16", "p25", "p26", "p27", "p28", "p29", "p30", "p31", "p32"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that people with blood group O and B can donate to people with blood group B+. The output of the algorithm matches this expected set of rules.

# ### Who can donate to B-?
print ""
# In[22]:

rules = []
facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

goal = "donatestoB-"
positiveExamples = ["p5", "p6", "p7", "p8", "p21", "p22", "p23", "p24"]
negativeExamples = ["p1", "p2", "p3", "p4", "p9", "p10", "p11", "p12", "p13", "p14", "p15", "p16", "p17", "p18", "p19", "p20", "p25", "p26", "p27", "p28", "p29", "p30", "p31", "p32"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that only people with blood group O- and B- can donate to people with blood group O+. The output of the algorithm matches this expected set of rules.

# ### Who can donate to A+?

# In[24]:
print ""
rules = []
facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

goal = "donatestoA+"
positiveExamples = ["p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8", "p9", "p10", "p11", "p12", "p13", "p14", "p15", "p16"]
negativeExamples = ["p17", "p18", "p19", "p20", "p21", "p22", "p23", "p24", "p25", "p26", "p27", "p28", "p29", "p30", "p31", "p32"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that people with blood group O and A can donate to people with blood group A+. The output of the algorithm matches this expected set of rules.

# ### Who can donate to A-?

# In[26]:
print ""
rules = []
facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

goal = "donatestoA-"
positiveExamples = ["p5", "p6", "p7", "p8", "p13", "p14", "p15", "p16"]
negativeExamples = ["p1", "p2", "p3", "p4", "p9", "p10", "p11", "p12", "p17", "p18", "p19", "p20", "p21", "p22", "p23", "p24", "p25", "p26", "p27", "p28", "p29", "p30", "p31", "p32"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that people with blood group O- and A- can donate to people with blood group A-. The output of the algorithm matches the expected output.

# ### Who can donate to AB+?

# In[28]:
print ""
rules = []
facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

goal = "donatestoAB+"
positiveExamples = ["p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8", "p9", "p10", "p11", "p12", "p13", "p14", "p15", "p16", "p17", "p18", "p19", "p20", "p21", "p22", "p23", "p24", "p25", "p26", "p27", "p28", "p29", "p30", "p31", "p32"]
negativeExamples = []
ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that anybody can donate to people with blood group AB+. The output of the algorithm is that a person can donate blood to someone with blood group is A, or if their Rh factor is positive, or if their Rh factor is negative. Although this set of rules is correct, it is not minimal. Simply "donatestoAB+ :- True" would suffice.

# ### Who can donate to AB-?
print ""
# In[30]:

rules = []
facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12, fact13, fact14, fact15, fact16, fact17, fact18, fact19, fact20, fact21, fact22, fact23, fact24, fact25, fact26, fact27, fact28, fact29, fact30, fact31, fact32, fact1_1, fact2_1, fact3_1, fact4_1, fact5_1, fact6_1, fact7_1, fact8_1, fact9_1, fact10_1, fact11_1, fact12_1, fact13_1, fact14_1, fact15_1, fact16_1, fact17_1, fact18_1, fact19_1, fact20_1, fact21_1, fact22_1, fact23_1, fact24_1, fact25_1, fact26_1, fact27_1, fact28_1, fact29_1, fact30_1, fact31_1, fact32_1]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)

goal = "donatestoAB-"
positiveExamples = ["p5", "p6", "p7", "p8", "p13", "p14", "p15", "p16", "p21", "p22", "p23", "p24", "p29", "p30", "p31", "p32"]
negativeExamples = ["p1", "p2", "p3", "p4", "p9", "p10", "p11", "p12", "p17", "p18", "p19", "p20", "p25", "p26", "p27", "p28"]
ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that anyone with Rh factor negative can donate to AB-. The output of the algorithm matches the expected output.

# ## Example 5 - Nested exception

# In[31]:

print "\nExample 5:\n"

rules = []
fact1 = Fact(predicate_arg = "bloodcancer", parameter_arg = "patient1")
fact2 = Fact(predicate_arg = "marrowdonated", parameter_arg = "patient1")
fact3 = Fact(predicate_arg = "marrowincompatible", parameter_arg = "patient1")

fact4 = Fact(predicate_arg = "bloodcancer", parameter_arg = "patient2")

fact5 = Fact(predicate_arg = "bloodcancer", parameter_arg = "patient3")
fact6 = Fact(predicate_arg = "marrowdonated", parameter_arg = "patient3")

facts = [fact1, fact2, fact3, fact4, fact5, fact6]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)
goal = "dies"
positiveExamples = ["patient1", "patient2"]
negativeExamples = ["patient3"]

predicateList = ["bloodcancer", "marrowdonated", "marrowincompatible"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that a person who has blood cancer will die, with the exception that someone has donated bone marrow to him. However, he will also die if the marrow donated is incompatible. The output of the algorithm matches the expected output.

# ## Example 6 - Nested exception

# In[32]:
print "\nExample 6:\n"

rule1 = Rule(head_arg = "givesinterview", body_arg = ["graduated"])
rules = [rule1]

fact1 = Fact(predicate_arg = "graduated", parameter_arg = "alice")
fact2 = Fact(predicate_arg = "graduated", parameter_arg = "bob")
fact3 = Fact(predicate_arg = "graduated", parameter_arg = "charlie")
fact4 = Fact(predicate_arg = "graduated", parameter_arg = "devon")

fact5 = Fact(predicate_arg = "lessGPA", parameter_arg = "alice")
fact6 = Fact(predicate_arg = "lessGPA", parameter_arg = "bob")
fact7 = Fact(predicate_arg = "lessGPA", parameter_arg = "charlie")

fact8 = Fact(predicate_arg = "personaldifficulty", parameter_arg = "alice")
fact9 = Fact(predicate_arg = "personaldifficulty", parameter_arg = "bob")

fact10 = Fact(predicate_arg = "givesinterview", parameter_arg = "frank")
fact11 = Fact(predicate_arg = "givesinterview", parameter_arg = "george")

fact12 = Fact(predicate_arg = "brilliant", parameter_arg = "frank")

facts = [fact1, fact2, fact3, fact4, fact5, fact6, fact7, fact8, fact9, fact10, fact11, fact12]

bk = BackgroundKnowledge(rules_arg = rules, facts_arg = facts)
goal = "accepted"
positiveExamples = ["alice", "bob", "devon", "frank"]
negativeExamples = ["charlie", "george"]

predicateList = ["givesinterview", "graduated", "lessGPA", "personaldifficulty", "brilliant"]

ab_count = 0
abnormalRules = []
result = FOLD(positiveExamples, negativeExamples, predicateList, bk)

prettyprint(result)


# #### The expected set of rules is that a person who has graduated but has a low GPA will be rejected, unless his/her GPA has dropped because of personal difficulties. Also, if a person has not graduated but is brilliant, he/she will be accepted.
