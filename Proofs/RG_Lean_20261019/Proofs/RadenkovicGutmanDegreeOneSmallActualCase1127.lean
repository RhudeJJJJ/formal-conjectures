/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1127 : Family 8 := level8.get ⟨167,by decide⟩
def sourceMap1127 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,4,5,6,7,2,3] (sourceLabel 8 0 0 v)
def fusedMap1127 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap1127_checked : acceptsGraphIso
    (source (graph core1127) (root 8) 0 0) SmallGeFourSpectrum047.graph sourceMap1127=true := by decide +kernel
theorem fusedMap1127_checked : acceptsGraphIso
    (fused (graph core1127) (root 8) 0 0) SmallGeFourSpectrum067.graph fusedMap1127=true := by decide +kernel
theorem certified1127 : Certified (graph core1127) (root 8) 0 0 :=
  of_native_maps core1127 SmallGeFourSpectrum047.graph SmallGeFourSpectrum067.graph
    sourceMap1127 fusedMap1127 sourceMap1127_checked fusedMap1127_checked
    DegreeOneSmallComparisons.comparison1127
#print axioms sourceMap1127_checked
#print axioms fusedMap1127_checked
#print axioms certified1127
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
