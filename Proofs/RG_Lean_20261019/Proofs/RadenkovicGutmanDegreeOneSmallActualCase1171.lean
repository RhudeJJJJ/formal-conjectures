/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1171 : Family 8 := level8.get ⟨210,by decide⟩
def sourceMap1171 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1171 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1171_checked : acceptsGraphIso
    (source (graph core1171) (root 8) 0 0) SmallGeFourSpectrum083.graph sourceMap1171=true := by decide +kernel
theorem fusedMap1171_checked : acceptsGraphIso
    (fused (graph core1171) (root 8) 0 0) SmallGeFourSpectrum047.graph fusedMap1171=true := by decide +kernel
theorem certified1171 : Certified (graph core1171) (root 8) 0 0 :=
  of_native_maps core1171 SmallGeFourSpectrum083.graph SmallGeFourSpectrum047.graph
    sourceMap1171 fusedMap1171 sourceMap1171_checked fusedMap1171_checked
    DegreeOneSmallComparisons.comparison1171
#print axioms sourceMap1171_checked
#print axioms fusedMap1171_checked
#print axioms certified1171
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
