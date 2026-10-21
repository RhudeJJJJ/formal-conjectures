/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1255 : Family 9 := level9.get ⟨35,by decide⟩
def sourceMap1255 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,8,9,10,11,6,7,4,5] (sourceLabel 9 0 0 v)
def fusedMap1255 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1255_checked : acceptsGraphIso
    (source (graph core1255) (root 9) 0 0) DegreeOneSmallSpectrum469.graph sourceMap1255=true := by decide +kernel
theorem fusedMap1255_checked : acceptsGraphIso
    (fused (graph core1255) (root 9) 0 0) DegreeOneSmallSpectrum394.graph fusedMap1255=true := by decide +kernel
theorem certified1255 : Certified (graph core1255) (root 9) 0 0 :=
  of_native_maps core1255 DegreeOneSmallSpectrum469.graph DegreeOneSmallSpectrum394.graph
    sourceMap1255 fusedMap1255 sourceMap1255_checked fusedMap1255_checked
    DegreeOneSmallComparisons.comparison1255
#print axioms sourceMap1255_checked
#print axioms fusedMap1255_checked
#print axioms certified1255
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
