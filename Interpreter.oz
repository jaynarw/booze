% Statement
% Environment (User Variable -> variable)
% SAS (Equivalence class) [<x>, <y>, <z>]

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
              [var ident(y)
                [var ident(x)
                  [nop]
                ]
              ]
              [nop]
            ]
InitialStack = [semanticstack(Statement {Dictionary.new})]
proc {Execute SematicStack SingleAssignmentStore}
  % {Browse [SematicStack SingleAssignmentStore]}
  case SematicStack
  of StackHead|RemainingStack then
    case StackHead 
    of semanticstack(Statement Environment) then
      case Statement of H|T then
        if H == nop then
          {Browse [s k i p]}
          {Execute RemainingStack SingleAssignmentStore}
        elseif H == var then
          case T.1
          of ident(X) then
            {Browse [locaal(X) sin T.2.1]}
            {Dictionary.put Environment X {MaxList {Dictionary.keys SingleAssignmentStore}}+1}
            {Execute semanticstack(T.2.1 Environment)|RemainingStack SingleAssignmentStore}
          end
        else
          {Execute {Concat {Map Statement fun {$ A} semanticstack(A Environment) end} RemainingStack} SingleAssignmentStore}
        end
      end
    end
  end
end
{Execute InitialStack {Dictionary.new}}
{Browse {FoldL [2 3 4].2 Max [2 3 4].1}}