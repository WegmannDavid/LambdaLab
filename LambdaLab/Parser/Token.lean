
namespace LambdaLab.Parser

abbrev Restricted (P : String → Prop) : Type := { s : String // P s }

end LambdaLab.Parser
