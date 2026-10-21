/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core116 : Family 8 := level8.get ⟨186,by decide⟩
def sourceMap116 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap116 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,8,9,10,2,3,6,7,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap116_checked : acceptsGraphIso
    (source (graph core116) (root 8) 0 0) SmallGeFourSpectrum062.graph
      sourceMap116=true := by decide +kernel
theorem fusedMap116_checked : acceptsGraphIso
    (fused (graph core116) (root 8) 0 0) SmallGeFourSpectrum058.graph
      fusedMap116=true := by decide +kernel
theorem certified116 : Certified (graph core116) (root 8) 0 0 :=
  of_native_maps core116 SmallGeFourSpectrum062.graph SmallGeFourSpectrum058.graph
    sourceMap116 fusedMap116 sourceMap116_checked fusedMap116_checked
    SmallGeFourComparisons.comparison116
#print axioms sourceMap116_checked
#print axioms fusedMap116_checked
#print axioms certified116
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
