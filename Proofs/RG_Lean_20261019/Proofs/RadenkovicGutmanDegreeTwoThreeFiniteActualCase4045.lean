/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4045 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap4045 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,12,6,7,8,9,10,11] (sourceLabel 6 2 2 v)
def fusedMap4045 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap4045_checked : acceptsGraphIso
    (source (graph core4045) (root 6) 2 2) DegreeOneSmallSpectrum1274.graph sourceMap4045=true := by decide +kernel
theorem fusedMap4045_checked : acceptsGraphIso
    (fused (graph core4045) (root 6) 2 2) DegreeOneSmallSpectrum894.graph fusedMap4045=true := by decide +kernel
theorem certified4045 : Certified (graph core4045) (root 6) 2 2 :=
  of_native_maps core4045 DegreeOneSmallSpectrum1274.graph DegreeOneSmallSpectrum894.graph
    sourceMap4045 fusedMap4045 sourceMap4045_checked fusedMap4045_checked
    DegreeTwoThreeFiniteComparisons.comparison4045
#print axioms sourceMap4045_checked
#print axioms fusedMap4045_checked
#print axioms certified4045
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
