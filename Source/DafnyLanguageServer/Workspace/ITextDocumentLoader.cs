﻿using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations are responsible to load a specified language server document and generate
  /// a dafny document out of it.
  /// </summary>
  public interface ITextDocumentLoader {
    /// <summary>
    /// Creates a dafny document from the given text document without loading it.
    /// </summary>
    /// <param name="textDocument">The text document to create the unloaded document from.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The unloaded dafny document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    DafnyDocument CreateUnloaded(TextDocumentItem textDocument, CancellationToken cancellationToken);

    /// <summary>
    /// Loads the specified document item of the language server and applies the necessary steps
    /// to generate a dafny document instance.
    /// </summary>
    /// <param name="textDocument">The text document to load.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// 
    /// <returns>The loaded dafny document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken);

    /// <summary>
    /// Verifies the given document.
    /// </summary>
    /// <param name="document">The document to verify.</param>
    /// <param name="cancellationToken">A token to cancel the verification before its completion.</param>
    /// <returns>A new document instance including the verification results.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Task<DafnyDocument> VerifyAsync(DafnyDocument document, CancellationToken cancellationToken);
  }
}
