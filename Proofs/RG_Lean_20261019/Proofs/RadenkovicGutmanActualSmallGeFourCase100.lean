/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core100 : Family 7 := level7.get ⟨113,by decide⟩
def sourceMap100 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,8,9,1,2,3,4,5,6,7] (sourceLabel 7 0 0 v)
def fusedMap100 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,5,6,7,8,9,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap100_checked : acceptsGraphIso
    (source (graph core100) (root 7) 0 0) SmallGeFourSpectrum024.graph
      sourceMap100=true := by decide +kernel
theorem fusedMap100_checked : acceptsGraphIso
    (fused (graph core100) (root 7) 0 0) SmallGeFourSpectrum035.graph
      fusedMap100=true := by decide +kernel
theorem certified100 : Certified (graph core100) (root 7) 0 0 :=
  of_native_maps core100 SmallGeFourSpectrum024.graph SmallGeFourSpectrum035.graph
    sourceMap100 fusedMap100 sourceMap100_checked fusedMap100_checked
    SmallGeFourComparisons.comparison100
#print axioms sourceMap100_checked
#print axioms fusedMap100_checked
#print axioms certified100
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
