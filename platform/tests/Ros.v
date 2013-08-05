Require Import Bedrock Xml.
Export Bedrock Xml.


(** * Requests *)

Definition ptype (name : string) (p : pat) : pat := (
  "value"/(name/p)
)%pat.

Definition pint := ptype "int".
Definition pboolean := ptype "boolean".
Definition pstring := ptype "string".

Notation "!int x" := (pint x%pat) (at level 0, x at level 0) : pat_scope.
Notation "!boolean x" := (pboolean x%pat) (at level 0, x at level 0) : pat_scope.
Notation "!string x" := (pstring x%pat) (at level 0, x at level 0) : pat_scope.

Fixpoint params' (ps : list pat) : pat :=
  match ps with
    | nil => ""
    | p :: nil => "param"/p
    | p :: ps' => ("param"/p);;params' ps'
  end%pat.

Definition params (ps : list pat) : pat := (
  "params"/(params' ps)
)%pat.

Definition request (methodName : string) (ps : list pat) : pat := (
  "methodCall"/(
    "methodName"/methodName
    & params ps
  )
)%pat.


(** * Responses *)

Inductive outcome := Success | UserError | ServerError.

Definition outcomeToXml (o : outcome) : xml :=
  match o with
    | Success => "1"
    | UserError => "-1"
    | ServerError => "0"
  end.

Coercion outcomeToXml : outcome >-> xml.

Definition response (o : outcome) (msg body : xml) : action := (
  Write <*> "methodResponse" </>
    <*> "params" </>
      <*> "param" </>
        <*> "value" </>
          <*> "array" </>
            <*> "data" </>
              <*> "value" </>
                <*> "int" </>
                  o
                </>
              </>,
              <*> "value" </>
                <*> "string" </>
                  msg
                </>
              </>,
              <*> "value" </>
                body
              </>
            </>
          </>
        </>
      </>
    </>
  </>
)%action.

Notation "'Response' o 'Message' msg 'Body' body 'end'" :=
  (response o msg%out body%out)
  (at level 0, o at level 0, msg at level 0, body at level 0) : action_scope.

Definition rarray (body : xml) : xml := (
  <*> "array" </>
    <*> "data" </>
      body
    </>
  </>
)%out.

Definition afrom tab cond body := (
  rarray From tab Where cond Write body
)%out.

Definition rtype (name : string) (body : xml) := (
  <*> name </>
    body
  </>
)%out.

Definition rint := rtype "int".
Definition rboolean := rtype "boolean".
Definition rstring := rtype "string".

Notation "!int x" := (rint x%out) (at level 0, x at level 0) : out_scope.
Notation "!boolean x" := (rboolean x%out) (at level 0, x at level 0) : out_scope.
Notation "!string x" := (rstring x%out) (at level 0, x at level 0) : out_scope.

Definition rtrue := rboolean "true".
Definition rfalse := rboolean "false".

Notation "!true" := rtrue : out_scope.
Notation "!false" := rfalse : out_scope.

Notation "'ArrayFrom' tab 'Where' cond 'Write' o" :=
  (afrom tab cond%condition o%out)
  (at level 0, tab at level 0, cond at level 0, o at level 0) : out_scope.

Notation "'ArrayFrom' tab 'Write' o" :=
  (afrom tab nil o%out)
  (at level 0, tab at level 0, o at level 0) : out_scope.

Definition ignore := ""%out.


(** * Combined notation *)

Notation "'RosCommand' cmd () 'Do' a 'end'" :=
  (Rule (request cmd nil) a%action)
  (at level 0, cmd at level 0) : program_scope.

Notation "'RosCommand' cmd ( p1 , .. , pN ) 'Do' a 'end'" :=
  (Rule (request cmd (cons p1%pat .. (cons pN%pat nil) ..)) a%action)
  (at level 0, cmd at level 0) : program_scope.
