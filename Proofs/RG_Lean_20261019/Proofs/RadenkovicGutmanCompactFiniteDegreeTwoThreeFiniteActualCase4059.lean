/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4059 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap4059 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap4059 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4059_checked : acceptsGraphIso
    (source (graph core4059) (root 6) 2 2) DegreeOneSmallSpectrum1980.graph sourceMap4059=true := by decide +kernel
theorem fusedMap4059_checked : acceptsGraphIso
    (fused (graph core4059) (root 6) 2 2) DegreeOneSmallSpectrum1088.graph fusedMap4059=true := by decide +kernel
theorem certified4059 : Certified (graph core4059) (root 6) 2 2 :=
  of_native_maps core4059 DegreeOneSmallSpectrum1980.graph DegreeOneSmallSpectrum1088.graph
    sourceMap4059 fusedMap4059 sourceMap4059_checked fusedMap4059_checked
    DegreeTwoThreeFiniteComparisons.comparison4059
#print axioms sourceMap4059_checked
#print axioms fusedMap4059_checked
#print axioms certified4059
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
