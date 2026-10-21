/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0416 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0416 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0416 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0416_checked : acceptsGraphIso
    (source (graph core0416) (root 6) 1 1) DegreeOneSmallSpectrum288.graph sourceMap0416=true := by decide +kernel
theorem fusedMap0416_checked : acceptsGraphIso
    (fused (graph core0416) (root 6) 1 1) DegreeOneSmallSpectrum177.graph fusedMap0416=true := by decide +kernel
theorem certified0416 : Certified (graph core0416) (root 6) 1 1 :=
  of_native_maps core0416 DegreeOneSmallSpectrum288.graph DegreeOneSmallSpectrum177.graph
    sourceMap0416 fusedMap0416 sourceMap0416_checked fusedMap0416_checked
    DegreeOneSmallComparisons.comparison0416
#print axioms sourceMap0416_checked
#print axioms fusedMap0416_checked
#print axioms certified0416
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
