/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4047 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap4047 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,7,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap4047 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4047_checked : acceptsGraphIso
    (source (graph core4047) (root 6) 2 2) DegreeOneSmallSpectrum1458.graph sourceMap4047=true := by decide +kernel
theorem fusedMap4047_checked : acceptsGraphIso
    (fused (graph core4047) (root 6) 2 2) DegreeOneSmallSpectrum961.graph fusedMap4047=true := by decide +kernel
theorem certified4047 : Certified (graph core4047) (root 6) 2 2 :=
  of_native_maps core4047 DegreeOneSmallSpectrum1458.graph DegreeOneSmallSpectrum961.graph
    sourceMap4047 fusedMap4047 sourceMap4047_checked fusedMap4047_checked
    DegreeTwoThreeFiniteComparisons.comparison4047
#print axioms sourceMap4047_checked
#print axioms fusedMap4047_checked
#print axioms certified4047
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
