/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0276 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0276 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,1,0,5,6,7,8,3,4] (sourceLabel 6 0 0 v)
def fusedMap0276 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,5,0,1,2,3,4,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0276_checked : acceptsGraphIso
    (source (graph core0276) (root 6) 0 0) DegreeOneSmallSpectrum048.graph sourceMap0276=true := by decide +kernel
theorem fusedMap0276_checked : acceptsGraphIso
    (fused (graph core0276) (root 6) 0 0) DegreeOneSmallSpectrum034.graph fusedMap0276=true := by decide +kernel
theorem certified0276 : Certified (graph core0276) (root 6) 0 0 :=
  of_native_maps core0276 DegreeOneSmallSpectrum048.graph DegreeOneSmallSpectrum034.graph
    sourceMap0276 fusedMap0276 sourceMap0276_checked fusedMap0276_checked
    DegreeOneSmallComparisons.comparison0276
#print axioms sourceMap0276_checked
#print axioms fusedMap0276_checked
#print axioms certified0276
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
