/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0142 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0142 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 4 3 3 v)
def fusedMap0142 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 3 3 v)
theorem sourceMap0142_checked : acceptsGraphIso
    (source (graph core0142) (root 4) 3 3) DegreeOneSmallSpectrum1510.graph sourceMap0142=true := by decide +kernel
theorem fusedMap0142_checked : acceptsGraphIso
    (fused (graph core0142) (root 4) 3 3) DegreeOneSmallSpectrum857.graph fusedMap0142=true := by decide +kernel
theorem certified0142 : Certified (graph core0142) (root 4) 3 3 :=
  of_native_maps core0142 DegreeOneSmallSpectrum1510.graph DegreeOneSmallSpectrum857.graph
    sourceMap0142 fusedMap0142 sourceMap0142_checked fusedMap0142_checked
    DegreeOneSmallComparisons.comparison0142
#print axioms sourceMap0142_checked
#print axioms fusedMap0142_checked
#print axioms certified0142
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
