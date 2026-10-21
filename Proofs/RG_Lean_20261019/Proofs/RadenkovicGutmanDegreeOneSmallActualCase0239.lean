/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0239 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0239 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 1 3 v)
def fusedMap0239 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0239_checked : acceptsGraphIso
    (source (graph core0239) (root 5) 1 3) DegreeOneSmallSpectrum506.graph sourceMap0239=true := by decide +kernel
theorem fusedMap0239_checked : acceptsGraphIso
    (fused (graph core0239) (root 5) 1 3) DegreeOneSmallSpectrum379.graph fusedMap0239=true := by decide +kernel
theorem certified0239 : Certified (graph core0239) (root 5) 1 3 :=
  of_native_maps core0239 DegreeOneSmallSpectrum506.graph DegreeOneSmallSpectrum379.graph
    sourceMap0239 fusedMap0239 sourceMap0239_checked fusedMap0239_checked
    DegreeOneSmallComparisons.comparison0239
#print axioms sourceMap0239_checked
#print axioms fusedMap0239_checked
#print axioms certified0239
def sourceMap0239swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (sourceLabel 5 3 1 v)
def fusedMap0239swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0239swap_checked : acceptsGraphIso
    (source (graph core0239) (root 5) 3 1) DegreeOneSmallSpectrum506.graph sourceMap0239swap=true := by decide +kernel
theorem fusedMap0239swap_checked : acceptsGraphIso
    (fused (graph core0239) (root 5) 3 1) DegreeOneSmallSpectrum379.graph fusedMap0239swap=true := by decide +kernel
theorem certified0239swap : Certified (graph core0239) (root 5) 3 1 :=
  of_native_maps core0239 DegreeOneSmallSpectrum506.graph DegreeOneSmallSpectrum379.graph
    sourceMap0239swap fusedMap0239swap sourceMap0239swap_checked fusedMap0239swap_checked
    DegreeOneSmallComparisons.comparison0239
#print axioms sourceMap0239swap_checked
#print axioms fusedMap0239swap_checked
#print axioms certified0239swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
