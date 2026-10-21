/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core054 : Family 6 := level6.get ⟨47,by decide⟩
def sourceMap054 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap054 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap054_checked : acceptsGraphIso
    (source (graph core054) (root 6) 0 0) SmallGeFourSpectrum014.graph
      sourceMap054=true := by decide +kernel
theorem fusedMap054_checked : acceptsGraphIso
    (fused (graph core054) (root 6) 0 0) SmallGeFourSpectrum008.graph
      fusedMap054=true := by decide +kernel
theorem certified054 : Certified (graph core054) (root 6) 0 0 :=
  of_native_maps core054 SmallGeFourSpectrum014.graph SmallGeFourSpectrum008.graph
    sourceMap054 fusedMap054 sourceMap054_checked fusedMap054_checked
    SmallGeFourComparisons.comparison054
#print axioms sourceMap054_checked
#print axioms fusedMap054_checked
#print axioms certified054
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
