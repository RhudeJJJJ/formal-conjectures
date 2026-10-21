/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0126 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0126 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 4 3 3 v)
def fusedMap0126 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 3 3 v)
theorem sourceMap0126_checked : acceptsGraphIso
    (source (graph core0126) (root 4) 3 3) DegreeOneSmallSpectrum1509.graph sourceMap0126=true := by decide +kernel
theorem fusedMap0126_checked : acceptsGraphIso
    (fused (graph core0126) (root 4) 3 3) DegreeOneSmallSpectrum856.graph fusedMap0126=true := by decide +kernel
theorem certified0126 : Certified (graph core0126) (root 4) 3 3 :=
  of_native_maps core0126 DegreeOneSmallSpectrum1509.graph DegreeOneSmallSpectrum856.graph
    sourceMap0126 fusedMap0126 sourceMap0126_checked fusedMap0126_checked
    DegreeOneSmallComparisons.comparison0126
#print axioms sourceMap0126_checked
#print axioms fusedMap0126_checked
#print axioms certified0126
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
