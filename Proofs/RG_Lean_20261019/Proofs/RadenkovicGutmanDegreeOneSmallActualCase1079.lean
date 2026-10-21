/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1079 : Family 8 := level8.get ⟨141,by decide⟩
def sourceMap1079 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1079 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1079_checked : acceptsGraphIso
    (source (graph core1079) (root 8) 0 0) SmallGeFourSpectrum052.graph sourceMap1079=true := by decide +kernel
theorem fusedMap1079_checked : acceptsGraphIso
    (fused (graph core1079) (root 8) 0 0) SmallGeFourSpectrum062.graph fusedMap1079=true := by decide +kernel
theorem certified1079 : Certified (graph core1079) (root 8) 0 0 :=
  of_native_maps core1079 SmallGeFourSpectrum052.graph SmallGeFourSpectrum062.graph
    sourceMap1079 fusedMap1079 sourceMap1079_checked fusedMap1079_checked
    DegreeOneSmallComparisons.comparison1079
#print axioms sourceMap1079_checked
#print axioms fusedMap1079_checked
#print axioms certified1079
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
