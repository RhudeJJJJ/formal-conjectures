/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4473 : Family 10 := level10.get ⟨185,by decide⟩
def sourceMap4473 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4473 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (fusedLabel 10 2 2 v)
theorem sourceMap4473_checked : acceptsGraphIso
    (source (graph core4473) (root 10) 2 2) DegreeTwoThreeSpectrum6798.graph sourceMap4473=true := by decide +kernel
theorem fusedMap4473_checked : acceptsGraphIso
    (fused (graph core4473) (root 10) 2 2) DegreeTwoThreeSpectrum5124.graph fusedMap4473=true := by decide +kernel
theorem certified4473 : Certified (graph core4473) (root 10) 2 2 :=
  of_native_maps core4473 DegreeTwoThreeSpectrum6798.graph DegreeTwoThreeSpectrum5124.graph
    sourceMap4473 fusedMap4473 sourceMap4473_checked fusedMap4473_checked
    DegreeTwoThreeFiniteComparisons.comparison4473
#print axioms sourceMap4473_checked
#print axioms fusedMap4473_checked
#print axioms certified4473
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
