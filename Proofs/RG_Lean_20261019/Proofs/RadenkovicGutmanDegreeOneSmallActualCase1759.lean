/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1759 : Family 9 := level9.get ⟨630,by decide⟩
def sourceMap1759 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1759 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1759_checked : acceptsGraphIso
    (source (graph core1759) (root 9) 0 0) SmallGeFourSpectrum226.graph sourceMap1759=true := by decide +kernel
theorem fusedMap1759_checked : acceptsGraphIso
    (fused (graph core1759) (root 9) 0 0) SmallGeFourSpectrum164.graph fusedMap1759=true := by decide +kernel
theorem certified1759 : Certified (graph core1759) (root 9) 0 0 :=
  of_native_maps core1759 SmallGeFourSpectrum226.graph SmallGeFourSpectrum164.graph
    sourceMap1759 fusedMap1759 sourceMap1759_checked fusedMap1759_checked
    DegreeOneSmallComparisons.comparison1759
#print axioms sourceMap1759_checked
#print axioms fusedMap1759_checked
#print axioms certified1759
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
