% Statement
% Environment (User Variable -> variable)
% SAS (Equivalence class) [<x>, <y>, <z>]
% \insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'

declare Statement InitialStack Execute Concat MaxList
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
Statement = [var ident(x) 
              [[var ident(y)
                [var ident(x)
                  [
                    [bind ident(x) ident(y)]
                    [bind ident(x) literal(99)]
                  ]
                ]
              ]
              [nop]]
            ]
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
  % {Browse SematicStack}
  case SematicStack
  of StackHead|RemainingStack then
    case StackHead 
    of semanticstack(Statement Environment) then
      case Statement of H|T then
        if H == nop then
          {Browse [s k i p]}
          {Execute RemainingStack}
        elseif H == var then
          case T.1
          of ident(X) then
            % local NewVar in
            {Browse [locaal(X) sin T.2.1]}
            {Execute semanticstack(T.2.1 {Adjoin Environment environment(X:{InsertIntoSAS}) })|RemainingStack}
            % end
          end
        elseif H == bind then
          {Unify T.1 T.2.1 Environment}
          {Execute RemainingStack}
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
{PrettyPrint SAS}