Inductive day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

Definition next_working_day (d:day) : day :=
    match d with
        | monday \u21d2 tuesday
        | tuesday \u21d2 wednesday
        | wednesday \u21d2 thursday
        | thursday \u21d2 friday
        | friday \u21d2 monday
        | saturday \u21d2 monday
        | sunday \u21d2 monday
    end.

Compute (next_working_day friday).