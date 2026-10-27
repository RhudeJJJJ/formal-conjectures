/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4662 : Family 10 := level10.get ⟨778,by decide⟩
def sourceMap4662 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4662 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4662_checked : acceptsGraphIso
    (source (graph core4662) (root 10) 2 2) DegreeTwoThreeSpectrum7447.graph sourceMap4662=true := by decide +kernel
theorem fusedMap4662_checked : acceptsGraphIso
    (fused (graph core4662) (root 10) 2 2) DegreeTwoThreeSpectrum5557.graph fusedMap4662=true := by decide +kernel
theorem certified4662 : Certified (graph core4662) (root 10) 2 2 :=
  of_native_maps core4662 DegreeTwoThreeSpectrum7447.graph DegreeTwoThreeSpectrum5557.graph
    sourceMap4662 fusedMap4662 sourceMap4662_checked fusedMap4662_checked
    DegreeTwoThreeFiniteComparisons.comparison4662
#print axioms sourceMap4662_checked
#print axioms fusedMap4662_checked
#print axioms certified4662
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
