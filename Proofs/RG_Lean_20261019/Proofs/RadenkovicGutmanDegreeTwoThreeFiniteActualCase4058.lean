/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4058 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap4058 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap4058 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4058_checked : acceptsGraphIso
    (source (graph core4058) (root 6) 2 2) DegreeOneSmallSpectrum1978.graph sourceMap4058=true := by decide +kernel
theorem fusedMap4058_checked : acceptsGraphIso
    (fused (graph core4058) (root 6) 2 2) DegreeOneSmallSpectrum1015.graph fusedMap4058=true := by decide +kernel
theorem certified4058 : Certified (graph core4058) (root 6) 2 2 :=
  of_native_maps core4058 DegreeOneSmallSpectrum1978.graph DegreeOneSmallSpectrum1015.graph
    sourceMap4058 fusedMap4058 sourceMap4058_checked fusedMap4058_checked
    DegreeTwoThreeFiniteComparisons.comparison4058
#print axioms sourceMap4058_checked
#print axioms fusedMap4058_checked
#print axioms certified4058
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
