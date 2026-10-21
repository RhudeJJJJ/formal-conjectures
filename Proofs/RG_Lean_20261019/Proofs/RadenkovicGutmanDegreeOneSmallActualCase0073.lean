/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0073 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0073 : (Vertices 3 ⊕ Fin 4 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 3 3 3 v)
def fusedMap0073 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10,11] (fusedLabel 3 3 3 v)
theorem sourceMap0073_checked : acceptsGraphIso
    (source (graph core0073) (root 3) 3 3) DegreeOneSmallSpectrum585.graph sourceMap0073=true := by decide +kernel
theorem fusedMap0073_checked : acceptsGraphIso
    (fused (graph core0073) (root 3) 3 3) DegreeOneSmallSpectrum369.graph fusedMap0073=true := by decide +kernel
theorem certified0073 : Certified (graph core0073) (root 3) 3 3 :=
  of_native_maps core0073 DegreeOneSmallSpectrum585.graph DegreeOneSmallSpectrum369.graph
    sourceMap0073 fusedMap0073 sourceMap0073_checked fusedMap0073_checked
    DegreeOneSmallComparisons.comparison0073
#print axioms sourceMap0073_checked
#print axioms fusedMap0073_checked
#print axioms certified0073
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
