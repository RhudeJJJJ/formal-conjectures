/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core120 : Family 8 := level8.get ⟨206,by decide⟩
def sourceMap120 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap120 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap120_checked : acceptsGraphIso
    (source (graph core120) (root 8) 0 0) SmallGeFourSpectrum076.graph
      sourceMap120=true := by decide +kernel
theorem fusedMap120_checked : acceptsGraphIso
    (fused (graph core120) (root 8) 0 0) SmallGeFourSpectrum046.graph
      fusedMap120=true := by decide +kernel
theorem certified120 : Certified (graph core120) (root 8) 0 0 :=
  of_native_maps core120 SmallGeFourSpectrum076.graph SmallGeFourSpectrum046.graph
    sourceMap120 fusedMap120 sourceMap120_checked fusedMap120_checked
    SmallGeFourComparisons.comparison120
#print axioms sourceMap120_checked
#print axioms fusedMap120_checked
#print axioms certified120
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
