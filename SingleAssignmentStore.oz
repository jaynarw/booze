% Functions 
%  1. RetrieveFromSAS
%  2. BindRefToKeyInSAS
%  3. BindValueToKeyInSAS

declare SAS StoreCounter RetrieveFromSAS BindRefToKeyInSAS BindValueToKeyInSAS PrettyPrint GetFreeVars Uniq Concat ConcatLists
SAS = {Dictionary.new}
StoreCounter = {NewCell 0}

%% Auxilary Functions
fun {Concat Xs Ys}
  case Ys of H|T then
    {Concat H|Xs T}
  [] nil then Xs
  end
end
fun {ConcatLists Xs}
  {FoldL Xs Concat nil}
end

% ========================================
% X has been taken from the environment 
% ========================================
fun {InsertIntoSAS}
  {Assign StoreCounter @StoreCounter+1}
  {Dictionary.put SAS @StoreCounter equivalence(@StoreCounter)}
  @StoreCounter
end

% ========================================
% X has been taken from the environment 
% ========================================
fun {RetrieveFromSAS X}
  if {Dictionary.member SAS X} then
    {Dictionary.get SAS X}
  else
    raise keyNotFound(X) end
  end
end


% proc {BindSomeToKeyInRecord Replacement Match}


% end
fun {Uniq Xs}
  case Xs
  of nil then
    nil
  [] H|T then
    if {List.member H T} then
      {Uniq T}
    else
      H|{Uniq T}
    end
  else
    % {Browse [uniqcalledonnonlist Xs]}
    nil
  end
end

fun {FreeVarHelper Exp}
  % {Browse [infreevarhelper Exp]}
  case Exp of 
  ident(X) then 
    % {Browse X}
    [X]
  [] [pproc _ _] then
    {GetFreeVars Exp}
  [] H|T then
    {Uniq {Append {FreeVarHelper H} {FreeVarHelper T}}}
  else
    nil
  end
end

fun {GetFreeVars Stmt}
  case Stmt
  of [nop] then
    nil
  [] [var ident(X) S] then
    {Filter {GetFreeVars S} fun {$ A} A\=X end}
  [] [bind V1 V2] then
    % {Browse [freevar V1 V2]}
    % {Browse {Uniq {ConcatLists [{FreeVarHelper V1} {FreeVarHelper V2}]}}}
    {Uniq {ConcatLists [{FreeVarHelper V1} {FreeVarHelper V2}]}}
  [] [pproc IdentList S] then
    local VarsToFilter in 
      % {Browse IdentList}
      VarsToFilter = {Map IdentList fun {$ A} case A of ident(X) then X end end}
      {Filter {GetFreeVars S} fun {$ A} {List.member A VarsToFilter}==false end}
    end
  [] [match ident(X) P S1 S2] then
    {Uniq {ConcatLists [[X] {GetFreeVars S2} {Filter {GetFreeVars S1} fun {$ A} {List.member A {FreeVarHelper P}}==false end}]}}
  [] S1|S2 then
    {Uniq {ConcatLists [{GetFreeVars S1} {GetFreeVars S2}]}}
  [] nil then
    nil
  else
    % {Browse [unknownypeinfreevars Stmt]}
    nil
  end
end

% ========================================
% both X and Y are equivalence classes, 
% i.e., equivalence(X) and equivalence(Y)
% ========================================
proc {BindRefToKeyInSAS X Y}
  local KeysToModify in 
    KeysToModify = {Filter {Dictionary.entries SAS} fun {$ A} A.2 == equivalence(Y) end}
    {ForAll KeysToModify proc {$ A} {Dictionary.put SAS A.1 equivalence(X)} end}
  end
end

% ========================================
% Only X is a equivalence class, i.e., equivalence(X)
% and Exp2 is not an equivalence class
% ========================================
proc {BindValueToKeyInSAS X Exp2 Env}
  case Exp2 
  of literal(Y) then
    local KeysOfX KeysOfRecord in
      % {Browse 'In SAS literal'}
      KeysOfX = {Filter {Dictionary.entries SAS} fun {$ A} A.2 == equivalence(X) end}
      {ForAll KeysOfX proc {$ A} {Dictionary.put SAS A.1 literal(Y)} end}
      
      KeysOfRecord = {Filter {Dictionary.entries SAS} 
        fun {$ A} 
          case A.2 
          of H|_ then
            H == record
          else
            false  
          end
        end
      }
      {ForAll KeysOfRecord 
        proc {$ A}
          case A.2 
          of [record M N] then
            local New Features in
              if M == equivalence(X) then
                New = Exp2
              else
                New = M
              end
              Features = {Map N 
                fun {$ B}
                  {Map B 
                    fun {$ C} 
                      if C == equivalence(X) then
                        Exp2
                      else
                        C
                      end
                    end
                  } 
                end
              }
              {Dictionary.put SAS A.1 [record New Features]}
            end
          end
        end
      }
      
    end 
  [] [record Y Z] then
    local KeysOfX in
      % {Browse 'In SAS record'}
      KeysOfX = {Filter {Dictionary.entries SAS} fun {$ A} A.2 == equivalence(X) end}
      {ForAll KeysOfX proc {$ A} {Dictionary.put SAS A.1 [record Y Z]} end}
    end
  [] [pproc Y S] then
    local FreeVars ContextualEnv KeysOfX in 
      KeysOfX = {Filter {Dictionary.entries SAS} fun {$ A} A.2 == equivalence(X) end}
      FreeVars = {GetFreeVars [pproc Y S]}
      ContextualEnv = {List.toRecord environment {Map FreeVars fun {$ A} A#Env.A end}}
      % {Browse {Record.filterInd environment(a:1 c:2 d:5 e:1 b:0) fun {$ A} {List.member A [a b c]} end}}
      {ForAll KeysOfX proc {$ A} {Dictionary.put SAS A.1 pproc(code:[pproc Y S] contextualenv:ContextualEnv)} end}
    end
    % {Browse 'handle p r o c'}
  else
    {Browse [unkowntypeinvaltokey X Exp2 Env]}
  end
end

proc {PrettyPrint D}
  {ForAll {Dictionary.entries D} proc {$ A} {Browse [A.1 A.2]} end}
end
