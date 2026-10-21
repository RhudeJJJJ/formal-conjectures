/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core142 : Family 8 := level8.get ⟨262,by decide⟩
def sourceMap142 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap142 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,5,6,7,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap142_checked : acceptsGraphIso
    (source (graph core142) (root 8) 0 0) SmallGeFourSpectrum060.graph
      sourceMap142=true := by decide +kernel
theorem fusedMap142_checked : acceptsGraphIso
    (fused (graph core142) (root 8) 0 0) SmallGeFourSpectrum056.graph
      fusedMap142=true := by decide +kernel
theorem certified142 : Certified (graph core142) (root 8) 0 0 :=
  of_native_maps core142 SmallGeFourSpectrum060.graph SmallGeFourSpectrum056.graph
    sourceMap142 fusedMap142 sourceMap142_checked fusedMap142_checked
    SmallGeFourComparisons.comparison142
#print axioms sourceMap142_checked
#print axioms fusedMap142_checked
#print axioms certified142
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
