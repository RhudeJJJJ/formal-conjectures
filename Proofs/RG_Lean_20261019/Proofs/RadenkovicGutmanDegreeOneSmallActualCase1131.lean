/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1131 : Family 8 := level8.get ⟨171,by decide⟩
def sourceMap1131 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,4,5,6,7,2,3] (sourceLabel 8 0 0 v)
def fusedMap1131 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap1131_checked : acceptsGraphIso
    (source (graph core1131) (root 8) 0 0) SmallGeFourSpectrum048.graph sourceMap1131=true := by decide +kernel
theorem fusedMap1131_checked : acceptsGraphIso
    (fused (graph core1131) (root 8) 0 0) SmallGeFourSpectrum068.graph fusedMap1131=true := by decide +kernel
theorem certified1131 : Certified (graph core1131) (root 8) 0 0 :=
  of_native_maps core1131 SmallGeFourSpectrum048.graph SmallGeFourSpectrum068.graph
    sourceMap1131 fusedMap1131 sourceMap1131_checked fusedMap1131_checked
    DegreeOneSmallComparisons.comparison1131
#print axioms sourceMap1131_checked
#print axioms fusedMap1131_checked
#print axioms certified1131
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
