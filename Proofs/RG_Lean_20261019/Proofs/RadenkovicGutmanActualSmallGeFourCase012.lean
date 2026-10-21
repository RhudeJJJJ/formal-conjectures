/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core012 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap012 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,6,7,1,2,3,4,5] (sourceLabel 5 0 0 v)
def fusedMap012 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,5,6,7,3,4] (fusedLabel 5 0 0 v)
theorem sourceMap012_checked : acceptsGraphIso
    (source (graph core012) (root 5) 0 0) SmallGeFourSpectrum002.graph
      sourceMap012=true := by decide +kernel
theorem fusedMap012_checked : acceptsGraphIso
    (fused (graph core012) (root 5) 0 0) SmallGeFourSpectrum004.graph
      fusedMap012=true := by decide +kernel
theorem certified012 : Certified (graph core012) (root 5) 0 0 :=
  of_native_maps core012 SmallGeFourSpectrum002.graph SmallGeFourSpectrum004.graph
    sourceMap012 fusedMap012 sourceMap012_checked fusedMap012_checked
    SmallGeFourComparisons.comparison012
#print axioms sourceMap012_checked
#print axioms fusedMap012_checked
#print axioms certified012
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
