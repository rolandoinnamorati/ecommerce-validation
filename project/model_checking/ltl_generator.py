# Script per generare property.ltl
ltl_formula = "ltl no_deadlock { [] (" + " && ".join([f"<> (orders[{i}].date_ready > 0)" for i in range(3)]) + ") }"
with open("property.ltl", "w") as file:
    file.write(ltl_formula)