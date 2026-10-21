/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0219 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0219 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,4,5,6,7,2,3] (sourceLabel 5 0 0 v)
def fusedMap0219 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![5,0,1,2,3,4,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap0219_checked : acceptsGraphIso
    (source (graph core0219) (root 5) 0 0) DegreeOneSmallSpectrum031.graph sourceMap0219=true := by decide +kernel
theorem fusedMap0219_checked : acceptsGraphIso
    (fused (graph core0219) (root 5) 0 0) DegreeOneSmallSpectrum018.graph fusedMap0219=true := by decide +kernel
theorem certified0219 : Certified (graph core0219) (root 5) 0 0 :=
  of_native_maps core0219 DegreeOneSmallSpectrum031.graph DegreeOneSmallSpectrum018.graph
    sourceMap0219 fusedMap0219 sourceMap0219_checked fusedMap0219_checked
    DegreeOneSmallComparisons.comparison0219
#print axioms sourceMap0219_checked
#print axioms fusedMap0219_checked
#print axioms certified0219
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
