/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4865 : Family 10 := level10.get ⟨1288,by decide⟩
def sourceMap4865 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4865 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4865_checked : acceptsGraphIso
    (source (graph core4865) (root 10) 2 2) DegreeTwoThreeSpectrum7377.graph sourceMap4865=true := by decide +kernel
theorem fusedMap4865_checked : acceptsGraphIso
    (fused (graph core4865) (root 10) 2 2) DegreeTwoThreeSpectrum6561.graph fusedMap4865=true := by decide +kernel
theorem certified4865 : Certified (graph core4865) (root 10) 2 2 :=
  of_native_maps core4865 DegreeTwoThreeSpectrum7377.graph DegreeTwoThreeSpectrum6561.graph
    sourceMap4865 fusedMap4865 sourceMap4865_checked fusedMap4865_checked
    DegreeTwoThreeFiniteComparisons.comparison4865
#print axioms sourceMap4865_checked
#print axioms fusedMap4865_checked
#print axioms certified4865
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
