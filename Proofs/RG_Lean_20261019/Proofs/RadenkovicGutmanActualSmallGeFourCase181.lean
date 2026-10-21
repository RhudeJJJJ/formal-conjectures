/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core181 : Family 9 := level9.get ⟨414,by decide⟩
def sourceMap181 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap181 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap181_checked : acceptsGraphIso
    (source (graph core181) (root 9) 0 0) SmallGeFourSpectrum114.graph
      sourceMap181=true := by decide +kernel
theorem fusedMap181_checked : acceptsGraphIso
    (fused (graph core181) (root 9) 0 0) SmallGeFourSpectrum159.graph
      fusedMap181=true := by decide +kernel
theorem certified181 : Certified (graph core181) (root 9) 0 0 :=
  of_native_maps core181 SmallGeFourSpectrum114.graph SmallGeFourSpectrum159.graph
    sourceMap181 fusedMap181 sourceMap181_checked fusedMap181_checked
    SmallGeFourComparisons.comparison181
#print axioms sourceMap181_checked
#print axioms fusedMap181_checked
#print axioms certified181
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
