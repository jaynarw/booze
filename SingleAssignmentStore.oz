% Functions 
%  1. RetrieveFromSAS
%  2. BindRefToKeyInSAS
%  3. BindValueToKeyInSAS

declare SAS StoreCounter RetrieveFromSAS BindRefToKeyInSAS BindValueToKeyInSAS PrettyPrint
SAS = {Dictionary.new}
StoreCounter = {NewCell 0}

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
  {Dictionary.get SAS X}
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
proc {BindValueToKeyInSAS X Exp2}
  local KeysOfX in
    KeysOfX = {Filter {Dictionary.entries SAS} fun {$ A} A.2 == equivalence(X) end}
    {ForAll KeysOfX proc {$ A} {Dictionary.put SAS A.1 Exp2} end}
  end 
end

proc {PrettyPrint D}
  {ForAll {Dictionary.entries D} proc {$ A} {Browse [A.1 A.2]} end}
end