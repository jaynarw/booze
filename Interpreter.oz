% Statement
% Environment (User Variable -> variable)
% SAS (Equivalence class) [<x>, <y>, <z>]
% \insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'

declare Statement InitialStack Execute Concat MaxList MyCreateVars

fun {MyCreateVars Object}
  case Object of
    ident(X) then
      [X]
    [] [record RecordName Pairs] then
      local FromPairs in
        fun {FromPairs List}
          case List of
          H|T then
            {ConcatLists [{MyCreateVars H.1} {MyCreateVars H.2.1} {FromPairs T}]}
          [] nil then
            nil
          end
        end
        {Uniq {ConcatLists [{MyCreateVars RecordName} {FromPairs Pairs}]}}
      end
    else
      nil
  end
end

fun {Concat Xs Ys}
  {FoldR Xs fun {$ A B} A|B end Ys}
end
fun {MaxList Xs}
  if Xs == nil then
    0
  else
    {FoldL Xs.2 Max Xs.1}
  end
end
Statement = [var ident(copy)
              [var ident(a)
                  [var ident(b)
                    [[bind ident(copy) [pproc [ident(x) ident(y)] [bind ident(x) ident(y)]]]
                      [bind ident(b) literal(1)]
                      [apply ident(copy) ident(b) ident(a)]
                      [nop]]]]]

%%%%%%%%%%%%%%%%%%%%%%
% local X in
%   local Y in
%     local X in
%       X=Y
%     end
%   end
% end
%            
%%%%%%%%%%%%%%%%%%%%%%            
% Statement = [[nop] [nop] [nop] [nop]]
InitialStack = [semanticstack(Statement environment())]
proc {Execute SematicStack}
  {Browse SematicStack}
  case SematicStack
  of StackHead|RemainingStack then
    case StackHead 
    of semanticstack(Statement Environment) then
      case Statement of H|T then
        if H == nop then
          {Execute RemainingStack}
        elseif H == var then
          case T.1
          of ident(X) then
            {Execute semanticstack(T.2.1 {Adjoin Environment environment(X:{InsertIntoSAS}) })|RemainingStack}
          end
        elseif H == bind then
          {Unify T.1 T.2.1 Environment}
          {Execute RemainingStack}
        elseif H == match then
          case T of [ident(X) P S1 S2] then
            try
              local NewEnv in
                NewEnv = {Adjoin Environment {List.toRecord environment {Map {MyCreateVars P} fun {$ A} A#{InsertIntoSAS} end}}}
                {Unify ident(X) P NewEnv}
                {Execute semanticstack(S1 {Adjoin Environment NewEnv})|RemainingStack}
              end
            catch incompatibleTypes(A B) then
                {Execute semanticstack(S2 Environment)|RemainingStack}
            end
          end
        elseif H == apply then
          case T of
          ident(ProcName)|PassedArgs then
            local ProcToApply in
              ProcToApply = {RetrieveFromSAS Environment.ProcName}
              case ProcToApply
              of pproc(code:[pproc ProcArgs S] contextualenv:CE) then
                local NewEnv ZippedIdents in
                  ZippedIdents = {List.zip ProcArgs PassedArgs
                  fun {$ A B}
                    case A 
                    of ident(P) then
                      case B
                      of ident(Q) then
                        P#Environment.Q
                      end
                    end 
                  end}
                  NewEnv = {Adjoin CE {List.toRecord environment ZippedIdents}}
                  {Execute semanticstack(S NewEnv)|RemainingStack}
                end
              end
            end
          else
            raise invalidstmt(apply) end
          end
        else
          {Execute {Concat {Map Statement fun {$ A} semanticstack(A Environment) end} RemainingStack}}
        end
      end
    end
  else
    {Browse done}
  end
end
{Execute InitialStack}
{Browse '$$$$$$$ Printing SAS $$$$$$$$$'}
{PrettyPrint SAS}