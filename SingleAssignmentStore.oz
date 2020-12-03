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
  case Exp2 
  of literal(Y) then
    local KeysOfX KeysOfRecord in
      % {Browse 'In SAS literal'}
      KeysOfX = {Filter {Dictionary.entries SAS} fun {$ A} A.2 == equivalence(X) end}
      {ForAll KeysOfX proc {$ A} {Dictionary.put SAS A.1 literal(Y)} end}
      
      KeysOfRecord = {Filter {Dictionary.entries SAS} 
        fun {$ A} 
          case A.2 
          of H|T then
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
    {Browse 'handle p r o c'}
  end
end

proc {PrettyPrint D}
  {ForAll {Dictionary.entries D} proc {$ A} {Browse [A.1 A.2]} end}
end