/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0313 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0313 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0313 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0313_checked : acceptsGraphIso
    (source (graph core0313) (root 6) 0 1) DegreeOneSmallSpectrum105.graph sourceMap0313=true := by decide +kernel
theorem fusedMap0313_checked : acceptsGraphIso
    (fused (graph core0313) (root 6) 0 1) DegreeOneSmallSpectrum074.graph fusedMap0313=true := by decide +kernel
theorem certified0313 : Certified (graph core0313) (root 6) 0 1 :=
  of_native_maps core0313 DegreeOneSmallSpectrum105.graph DegreeOneSmallSpectrum074.graph
    sourceMap0313 fusedMap0313 sourceMap0313_checked fusedMap0313_checked
    DegreeOneSmallComparisons.comparison0313
#print axioms sourceMap0313_checked
#print axioms fusedMap0313_checked
#print axioms certified0313
def sourceMap0313swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0313swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0313swap_checked : acceptsGraphIso
    (source (graph core0313) (root 6) 1 0) DegreeOneSmallSpectrum105.graph sourceMap0313swap=true := by decide +kernel
theorem fusedMap0313swap_checked : acceptsGraphIso
    (fused (graph core0313) (root 6) 1 0) DegreeOneSmallSpectrum074.graph fusedMap0313swap=true := by decide +kernel
theorem certified0313swap : Certified (graph core0313) (root 6) 1 0 :=
  of_native_maps core0313 DegreeOneSmallSpectrum105.graph DegreeOneSmallSpectrum074.graph
    sourceMap0313swap fusedMap0313swap sourceMap0313swap_checked fusedMap0313swap_checked
    DegreeOneSmallComparisons.comparison0313
#print axioms sourceMap0313swap_checked
#print axioms fusedMap0313swap_checked
#print axioms certified0313swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
