/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1757 : Family 9 := level9.get ⟨629,by decide⟩
def sourceMap1757 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1757 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1757_checked : acceptsGraphIso
    (source (graph core1757) (root 9) 0 0) SmallGeFourSpectrum225.graph sourceMap1757=true := by decide +kernel
theorem fusedMap1757_checked : acceptsGraphIso
    (fused (graph core1757) (root 9) 0 0) SmallGeFourSpectrum163.graph fusedMap1757=true := by decide +kernel
theorem certified1757 : Certified (graph core1757) (root 9) 0 0 :=
  of_native_maps core1757 SmallGeFourSpectrum225.graph SmallGeFourSpectrum163.graph
    sourceMap1757 fusedMap1757 sourceMap1757_checked fusedMap1757_checked
    DegreeOneSmallComparisons.comparison1757
#print axioms sourceMap1757_checked
#print axioms fusedMap1757_checked
#print axioms certified1757
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
