class Circomspect < Formula
  desc "Static analyzer and linter for Circom"
  homepage "https://github.com/IceColdCasino/circomspect"
  url "https://github.com/IceColdCasino/circomspect/archive/refs/tags/v0.12.0.tar.gz"
  sha256 "b38b95a755d56bd702be3de843f95a8df77c594b25a01dccfabb9443b605f6b8"
  license "GPL-3.0-only"
  head "https://github.com/IceColdCasino/circomspect.git", branch: "main"

  depends_on "rust" => :build

  def install
    system "cargo", "install", *std_cargo_args(path: "cli")
  end

  test do
    assert_match "Circom", shell_output("#{bin}/circomspect --help")
  end
end
