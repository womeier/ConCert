From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import SpecializeChainBase.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import StringExtra.
From ConCert.Execution.Examples Require Import Escrow.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.Template Require Import Kernames All.

Import MonadNotation.

Open Scope string.

Instance EscrowMidlangBoxes : MidlangPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := true; (* full names to avoid clashes*)|}.

Notation "'eval_extract' x" :=
  ltac:(let x :=
            eval
              cbv
              beta
              delta [x receive RecordSet.set RecordSet.constructor Monads.bind Monads.Monad_option]
              iota in x in
       exact x) (at level 70).

Definition TT_escrow : list (kername * string) :=
  [    remap <%% bool %%> "Bool"
     ; remap <%% @Address %%> "Int"].

Definition midlang_translation_map :=
  Eval compute in
        [(<%% @current_slot %%>, "current_slot");
        (<%% @account_balance %%>, "account_balance");
        (<%% @address_eqb %%>, "Order.eq");
        (<%% @ctx_amount %%>, "ctx_amount");
        (<%% @ctx_from %%>, "ctx_from");
        (<%% @Chain %%>, "ConCertChain");
        (<%% @ContractCallContext %%>, "ConCertCallContext");
        (<%% @ConCert.Execution.Blockchain.ActionBody %%>, "ConCertAction");
        (<%% @ChainBase %%>, "ChainBaseWTF");
        (<%% @ctx_contract_address %%>, "contract_address");
        (<%% @Amount %%>,"Z" )].

Definition midlang_escrow_translate (name : kername) : option string :=
  match find (fun '(key, _) => eq_kername key name) (TT_escrow ++ midlang_translation_map) with
  | Some (_, val) => Some val
  | None => None
  end.

Axiom extraction_chain_base : ChainBase.
Existing Instance extraction_chain_base.

Definition escrow_init :=
  eval_extract @Escrow.init.

Definition escrow_receive :=
  eval_extract @Escrow.receive.

Definition escrow_name := Eval compute in <%% escrow_receive %%>.


MetaCoq Run (p <- tmQuoteRecTransp escrow_receive false ;;
             tmDefinition "escrow_env" p.1).

Definition ignored_concert_types :=
  Eval compute in
        [<%% @ActionBody %%>;
         <%% @Address %%>;
         <%% @Amount %%>;
         <%% @ChainBase %%>;
         <%% @Chain %%>;
         <%% @ContractCallContext %%>;
         <%% @SerializedValue %%>].

Import ResultMonad.

Definition extract_template_env_specalize
           (params : extract_template_env_params)
           (Σ : T.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := T2P.trans_global_decls Σ in
  Σ <- specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

Definition escrow_extract :=
  extract_template_env_specalize extract_within_coq
      escrow_env
      (KernameSet.singleton escrow_name)
       (fun kn => contains kn (ignored_concert_types
                             ++ map fst midlang_translation_map
                             ++ map fst TT_escrow)).

Definition wrap_in_delimiters s :=
  String.concat nl ["";"{-START-} "; s; "{-END-}"].


Definition midlang_prelude :=
  String.concat nl
                ["import Basics exposing (..)";
                "import Blockchain exposing (..)";
                "import Bool exposing (..)";
                "import Int exposing (..)";
                "import Maybe exposing (..)";
                "import Order exposing (..)";
                "import Transaction exposing (..)";
                "import Tuple exposing (..)";
                "";
                "-- some dummy definitions (will be remapped properly in the future)";
                "type AccountAddress = Int";
                "type ConCertAction = Act_transfer Int Z";
                "type ConCertCallContext = CCtx Unit";
                "type ConCertChain = CChain Unit";
                "ctx_from ctx = 0";
                "ctx_amount ctx = (Zpos (XO XH))";
                "contract_address _ = 0";
                "account_balance _ _ = (Zpos (XO XH))";
                "current_slot _ = O"
].

Definition escrow_result :=
  Eval vm_compute in
    (env <- escrow_extract ;;
     '(_, s) <- finish_print (print_env env midlang_escrow_translate);;
     ret s).

MetaCoq Run (match escrow_result with
             | Ok s => tmMsg "Extraction of escrow succeeded"
             | Err err => tmFail err
             end).

Definition midlang_escrow :=
  match escrow_result with
  | Ok s => wrap_in_delimiters (midlang_prelude ++ nl ++ s)
  | Err s => s
  end.

Redirect "./extraction/examples/midlang-extract/MidlangEscrow.midlang" Compute midlang_escrow.
