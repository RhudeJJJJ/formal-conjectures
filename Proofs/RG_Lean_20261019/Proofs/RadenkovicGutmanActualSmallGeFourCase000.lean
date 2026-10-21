/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core000 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap000 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (sourceLabel 4 0 0 v)
def fusedMap000 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 4 0 0 v)
theorem sourceMap000_checked : acceptsGraphIso
    (source (graph core000) (root 4) 0 0) SmallGeFourSpectrum001.graph
      sourceMap000=true := by decide +kernel
theorem fusedMap000_checked : acceptsGraphIso
    (fused (graph core000) (root 4) 0 0) SmallGeFourSpectrum000.graph
      fusedMap000=true := by decide +kernel
theorem certified000 : Certified (graph core000) (root 4) 0 0 :=
  of_native_maps core000 SmallGeFourSpectrum001.graph SmallGeFourSpectrum000.graph
    sourceMap000 fusedMap000 sourceMap000_checked fusedMap000_checked
    SmallGeFourComparisons.comparison000
#print axioms sourceMap000_checked
#print axioms fusedMap000_checked
#print axioms certified000
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
