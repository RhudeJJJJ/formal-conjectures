/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0855 : Family 8 := level8.get ⟨39,by decide⟩
def sourceMap0855 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap0855 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0855_checked : acceptsGraphIso
    (source (graph core0855) (root 8) 0 0) DegreeOneSmallSpectrum277.graph sourceMap0855=true := by decide +kernel
theorem fusedMap0855_checked : acceptsGraphIso
    (fused (graph core0855) (root 8) 0 0) DegreeOneSmallSpectrum176.graph fusedMap0855=true := by decide +kernel
theorem certified0855 : Certified (graph core0855) (root 8) 0 0 :=
  of_native_maps core0855 DegreeOneSmallSpectrum277.graph DegreeOneSmallSpectrum176.graph
    sourceMap0855 fusedMap0855 sourceMap0855_checked fusedMap0855_checked
    DegreeOneSmallComparisons.comparison0855
#print axioms sourceMap0855_checked
#print axioms fusedMap0855_checked
#print axioms certified0855
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
