/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4057 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap4057 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap4057 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4057_checked : acceptsGraphIso
    (source (graph core4057) (root 6) 2 2) DegreeOneSmallSpectrum1977.graph sourceMap4057=true := by decide +kernel
theorem fusedMap4057_checked : acceptsGraphIso
    (fused (graph core4057) (root 6) 2 2) DegreeOneSmallSpectrum992.graph fusedMap4057=true := by decide +kernel
theorem certified4057 : Certified (graph core4057) (root 6) 2 2 :=
  of_native_maps core4057 DegreeOneSmallSpectrum1977.graph DegreeOneSmallSpectrum992.graph
    sourceMap4057 fusedMap4057 sourceMap4057_checked fusedMap4057_checked
    DegreeTwoThreeFiniteComparisons.comparison4057
#print axioms sourceMap4057_checked
#print axioms fusedMap4057_checked
#print axioms certified4057
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
