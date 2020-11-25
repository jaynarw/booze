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
              [[var ident(y)
                [var ident(x)
                  [nop]
                ]
              ]
              [nop]]
            ]
InitialStack = [semanticstack(Statement environment())]
proc {Execute SematicStack SingleAssignmentStore}
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
            local NewVar in
              NewVar = {MaxList {Dictionary.items SingleAssignmentStore}}+1
              {Browse [locaal(X) sin T.2.1]}
              {Dictionary.put SingleAssignmentStore X NewVar}
              {Execute semanticstack(T.2.1 {Adjoin Environment environment(X:NewVar) })|RemainingStack SingleAssignmentStore}
            end
          end
        else
          {Execute {Concat {Map Statement fun {$ A} semanticstack(A Environment) end} RemainingStack} SingleAssignmentStore}
        end
      end
    end
  else
    {Browse done}
  end
end
{Execute InitialStack {Dictionary.new}}