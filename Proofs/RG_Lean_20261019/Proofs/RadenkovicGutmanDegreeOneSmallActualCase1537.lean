/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1537 : Family 9 := level9.get ⟨267,by decide⟩
def sourceMap1537 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1537 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1537_checked : acceptsGraphIso
    (source (graph core1537) (root 9) 0 0) SmallGeFourSpectrum162.graph sourceMap1537=true := by decide +kernel
theorem fusedMap1537_checked : acceptsGraphIso
    (fused (graph core1537) (root 9) 0 0) SmallGeFourSpectrum108.graph fusedMap1537=true := by decide +kernel
theorem certified1537 : Certified (graph core1537) (root 9) 0 0 :=
  of_native_maps core1537 SmallGeFourSpectrum162.graph SmallGeFourSpectrum108.graph
    sourceMap1537 fusedMap1537 sourceMap1537_checked fusedMap1537_checked
    DegreeOneSmallComparisons.comparison1537
#print axioms sourceMap1537_checked
#print axioms fusedMap1537_checked
#print axioms certified1537
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
